# How the Macro Expander and Language Server Cooperate: Tracing "Go to References"

This document traces how the "go to references" LSP operation is implemented in
Lean 4, from the user clicking in their editor all the way down to the data
structures populated during elaboration. Along the way it addresses how source
spans are mapped to semantic information, how reference data is accumulated,
how incrementality works, and how macros complicate the picture.

## 1. Overview of the architecture

The Lean language server has a two-level architecture:

- A **watchdog** process manages the overall session and coordinates across
  files. It holds the aggregated `References` data structure that combines
  information from `.ilean` files (for already-built dependencies) and live
  **file worker** processes (for currently open files).

- Each open file gets a **file worker** process that incrementally elaborates
  the file and reports reference information back to the watchdog.

When the editor sends a `textDocument/references` request, the watchdog handles
it directly using its aggregated `References` data—it does not forward the
request to a file worker. This design means that cross-file reference lookups
work naturally: the watchdog already has reference data from every module.

## 2. The request path: from cursor position to results

### 2.1 The handler

The entry point is `handleReference` in `src/Lean/Server/Watchdog.lean:956`:

```lean
def handleReference (p : ReferenceParams) : ReaderT ReferenceRequestContext IO (Array Location) := do
  let some module := (← read).fileWorkerMods.get? p.textDocument.uri
    | return #[]
  let references := (← read).references
  let mut result := #[]
  for ident in references.findAt module p.position (includeStop := true) do
    let identRefs := references.referringTo ident p.context.includeDeclaration
    result := result.append <| identRefs.map (·.location)
  return result
```

This does three things:

1. **Map the document URI to a module name** using `fileWorkerMods`.
2. **Find identifiers at the cursor position** by calling `references.findAt`.
3. **Collect all references to those identifiers** across all modules by calling
   `references.referringTo`.

### 2.2 Finding identifiers at a position

`References.findAt` (`src/Lean/Server/References.lean:741`) delegates to
`ModuleRefs.findAt` (`line 180`), which does a linear scan over the module's
`RefIdent → RefInfo` map. For each identifier, `RefInfo.contains` checks
whether any of its stored definition/usage ranges contain the cursor position.
The ranges are ordinary LSP `Range` values (line/column pairs).

### 2.3 Collecting all references

`References.referringTo` (`line 779`) calls `allRefsFor`, which behaves
differently depending on the kind of identifier:

- For **constants** (`RefIdent.const`): searches across *all* modules, because a
  constant defined in module A can be referenced from module B.
- For **free variables** (`RefIdent.fvar`): searches only within the defining
  module, since free variables are file-local.

For each module that has references to the identifier, it collects the
definition location (if `includeDeclaration` is set) and all usage locations.

## 3. How source spans map to semantic information

The fundamental data structure connecting source text to semantics is the
**InfoTree** (`src/Lean/Elab/InfoTree/Types.lean:291`):

```lean
inductive InfoTree where
  | context (i : PartialContextInfo) (t : InfoTree)
  | node (i : Info) (children : PersistentArray InfoTree)
  | hole (mvarId : MVarId)
```

Every `node` carries an `Info` header, and every `Info` carries a `Syntax`
object (`Info.stx`). The `Syntax` carries `SourceInfo` at its leaves, which
records byte positions in the source file.

### 3.1 SourceInfo: original vs. synthetic

`SourceInfo` (`Init/Prelude.lean:4801`) has three forms:

```lean
inductive SourceInfo where
  | original (leading : Substring.Raw) (pos : String.Pos.Raw)
             (trailing : Substring.Raw) (endPos : String.Pos.Raw)
  | synthetic (pos : String.Pos.Raw) (endPos : String.Pos.Raw) (canonical := false)
  | none
```

- **`original`**: produced by the parser for tokens that appear literally in the
  source text. Includes surrounding whitespace.
- **`synthetic`**: produced by macro expansion or elaboration. Carries positions
  copied from the original syntax that triggered the expansion. The `canonical`
  flag (explained below) controls whether this synthetic position should be
  treated as "real" for hover/error purposes.
- **`none`**: no position information at all.

### 3.2 Position queries with `canonicalOnly`

The position accessors `SourceInfo.getPos?` and `SourceInfo.getTailPos?` take a
`canonicalOnly` parameter (`Init/Prelude.lean:4846`):

```lean
def getPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos.Raw :=
  match info, canonicalOnly with
  | original (pos := pos) ..,  _
  | synthetic (pos := pos) (canonical := true) .., _
  | synthetic (pos := pos) .., false => some pos
  | _,                         _     => none
```

When `canonicalOnly` is true, non-canonical synthetic positions are treated as
invisible. This is critical for the reference system: `Info.range?`
(`src/Lean/Server/InfoUtils.lean:204`) always passes `canonicalOnly := true`:

```lean
def Info.range? (i : Info) : Option Lean.Syntax.Range :=
  i.stx.getRange? (canonicalOnly := true)
```

This means that info nodes whose syntax has only non-canonical synthetic
positions will have no range and will be excluded from reference collection.

### 3.3 From Info nodes to RefIdents

The function `identOf` (`src/Lean/Server/References.lean:241`) maps an `Info`
node to a `RefIdent`:

```lean
def identOf (ci : ContextInfo) (i : Info) : Option (RefIdent × Bool) := do
  match i with
  | Info.ofTermInfo ti => match ti.expr with
    | Expr.const n .. =>
      some (RefIdent.const (← getModuleContainingDecl? ci.env n).toString n.toString, ti.isBinder)
    | Expr.fvar id =>
      some (RefIdent.fvar ci.env.header.mainModule.toString id.name.toString, ti.isBinder)
    | _ => none
  | Info.ofFieldInfo fi =>
    some (RefIdent.const (← getModuleContainingDecl? ci.env fi.projName).toString fi.projName.toString, false)
  | Info.ofOptionInfo oi => ...
  | Info.ofDocElabInfo dei => ...
  | _ => none
```

This is where the semantic mapping happens: a `TermInfo` node records the
fully elaborated `Expr`, so the system knows *which* constant or local variable
a particular source span refers to. The elaborator has already resolved
overloading, name resolution, and implicit arguments.

## 4. How reference data is accumulated

### 4.1 During elaboration: InfoTree construction

Reference data is **not accumulated as a separate data structure during
elaboration**. Instead, the elaborator builds the general-purpose `InfoTree`,
which records every elaborated term, tactic, command, and macro expansion as a
tree of `Info` nodes.

The `InfoState` (`src/Lean/Elab/InfoTree/Types.lean:310`) is carried in the
`CoreM` monad state. Key operations:

- **`pushInfoLeaf`** (`src/Lean/Elab/InfoTree/Main.lean:327`): adds a leaf
  `Info` node (no children). Used for individual term elaboration results.
- **`withInfoContext`** (`line 417`): runs an elaboration action while
  collecting all `InfoTree` nodes it produces as children of a new node. This
  is how nesting is expressed—elaborating a function application creates a node
  whose children include the info trees for the function and arguments.
- **`addConstInfo`** (`line 334`): convenience function that pushes a `TermInfo`
  leaf for a resolved constant reference.

### 4.2 After elaboration: reference extraction

After a command finishes elaborating (producing an `InfoTree`), the file worker
extracts references by calling `findModuleRefs` (`src/Lean/Server/References.lean:389`):

```lean
def findModuleRefs (text : FileMap) (trees : Array InfoTree) (localVars : Bool := true)
    (allowSimultaneousBinderUse := false) : ModuleRefs := Id.run do
  let mut refs :=
    dedupReferences (allowSimultaneousBinderUse := allowSimultaneousBinderUse) <|
    combineIdents trees <|
    findReferences text trees
  ...
```

This is a three-stage pipeline:

1. **`findReferences`** (`line 258`): traverses the InfoTree with `visitM'`,
   collecting every `Info` node that (a) has an `identOf` result and (b) has
   `original` SourceInfo at its head. This produces a flat array of `Reference`
   values.

2. **`combineIdents`** (`line 287`): merges identifiers that should be
   considered the same. Multiple different `FVarId`s or a mixture of an `FVarId`
   and a constant name can arise for the "same" binding—for instance, `where`
   clauses create both a local `FVar` and a top-level constant. This step uses a
   union-find–like algorithm keyed on overlapping source ranges, plus explicit
   `FVarAliasInfo` nodes from the InfoTree.

3. **`dedupReferences`** (`line 373`): groups references by (identifier, range)
   to handle cases where multiple elaborators produce info for the same span.

The result is a `ModuleRefs` (a `TreeMap RefIdent RefInfo`), mapping each
identifier to its definition location and array of usage locations within that
module.

### 4.3 Reporting to the watchdog

The file worker sends reference data to the watchdog via custom LSP
notifications (`src/Lean/Server/FileWorker.lean:152`):

- **`$/lean/ileanInfoUpdate`**: sent incrementally as new commands are
  elaborated. Contains the `ModuleRefs` accumulated so far.
- **`$/lean/ileanInfoFinal`**: sent when the file is fully elaborated. Provides
  the complete, authoritative reference data.
- **`$/lean/ileanHeaderSetupInfo`**: sent after processing imports. Contains
  direct import information.

The `mkIleanInfoNotification` function (`line 152`) calls `findModuleRefs`
followed by `toLspModuleRefs` to convert the data to a JSON-serializable form.

### 4.4 The aggregated References structure

The watchdog maintains a `References` structure
(`src/Lean/Server/References.lean:537`):

```lean
structure References where
  ileans : ILeanMap        -- from .ilean files of built dependencies
  workers : WorkerRefMap   -- from live file workers
```

When serving a query, `getModuleRefs?` (`line 689`) checks worker data first
(live, potentially incomplete) and falls back to ilean data (complete but
potentially stale). This ensures that the user sees up-to-date results for
files they're editing, while still having cross-project references from
built dependencies.

## 5. Incrementality

### 5.1 Command-level incrementality

Lean's language server processes files as a sequence of commands. When the user
edits a file, the server determines which commands were affected and
re-elaborates only those. This is described in `src/Lean/Language/Lean.lean`
(Note [Incremental Parsing], lines 21-78):

- The system identifies the first command whose syntax changed (conservatively
  going back two commands to handle grammar edge cases like docstrings).
- Unchanged commands reuse their previous snapshots, including their `InfoTree`
  contributions.
- Changed commands are re-elaborated, producing new `InfoTree`s.

### 5.2 Incremental reference reporting

The `reportSnapshots` function (`src/Lean/Server/FileWorker.lean:237`) walks the
snapshot tree as it becomes available:

- It accumulates `InfoTree`s from each finished snapshot.
- Each time a new `InfoTree` is produced, if the reporter has already started
  blocking (waiting for snapshots), it sends an incremental
  `$/lean/ileanInfoUpdate` notification with the new trees.
- At the end, it sends a `$/lean/ileanInfoFinal` with all trees.

On the watchdog side, `updateWorkerRefs` (`src/Lean/Server/References.lean:605`)
handles versioning:

- If the incoming version is **newer** than what's stored: replace everything.
- If the version is **equal**: merge the new references into existing ones (this
  is the incremental update case).
- If the version is **older**: ignore (stale data from a previous edit).

### 5.3 ILean files for cross-module references

For modules that are built but not currently open, reference data comes from
`.ilean` files (`src/Lean/Server/References.lean:206`). These are JSON files
containing the `ModuleRefs` and declaration information. They are generated
during compilation and loaded by the watchdog at startup or when dependencies
change.

The `Ilean` structure (`line 206`) contains:
- `module`: the module name
- `directImports`: import information
- `references`: the `ModuleRefs` map
- `decls`: declaration range information (for "parent declaration" display in
  the editor)

## 6. The role of macros and the difficulties they create

### 6.1 The core problem

Macros transform syntax before elaboration. This means the syntax that the
elaborator sees (and records in `Info` nodes) may be structurally different from
what the user wrote. For example, `do` notation desugars to a chain of `bind`
calls, `if h : p then ...` desugars to `dite`, and user-defined macros can
perform arbitrary syntax transformations.

This creates a fundamental tension: the user wants to interact with the *source*
syntax they wrote, but semantic information is attached to the *expanded*
syntax that was elaborated.

### 6.2 How the design handles this

The design uses two mechanisms to bridge the gap between surface syntax and
elaborated syntax for the purpose of reference collection:

#### Mechanism 1: Synthetic SourceInfo with position copying

When a macro constructs new syntax using quotations, the new syntax nodes get
**synthetic** `SourceInfo` that copies the position from the original syntax.
The function `SourceInfo.fromRef` (`Init/Prelude.lean:5311`) creates this:

```lean
def SourceInfo.fromRef (ref : Syntax) (canonical := false) : SourceInfo :=
  match canonical with
  | true =>
    match ref.getPos? true, ref.getTailPos? true with
    | some pos, some tailPos => .synthetic pos tailPos true
    | _,        _            => noncanonical ref
  | false => noncanonical ref
```

When a quotation produces an atom or identifier from an antiquotation
(i.e. `$x` inside `` `(...) ``), the resulting syntax gets `canonical := true`,
meaning "this synthetic node corresponds directly to something the user wrote."
The syntax quotation elaborator in `src/Lean/Elab/Quotation.lean` generates
code that calls `SourceInfo.fromRef` with `canonical := true` for antiquotation
splices.

#### Mechanism 2: The `.original` filter in `findReferences`

The reference collection function (`src/Lean/Server/References.lean:266`) has
this critical filter:

```lean
if info.stx.getHeadInfo matches .original .. then
```

This means: **only collect references whose syntax has `original` SourceInfo**.
Syntax produced by macro expansion gets `synthetic` SourceInfo, so it is
excluded. Only the identifiers that were literally written by the user in the
source file are recorded as references.

This is a clean solution to the macro problem. Consider what happens when the
user writes `if h : p then a else b`:

1. The parser produces syntax with `original` SourceInfo for `h`, `p`, `a`, `b`.
2. The macro expands this to `dite p (fun h => a) (fun h => b)`.
3. In the expanded syntax, `dite` gets `synthetic` SourceInfo (it wasn't in the
   original text). `p`, `a`, `b`, and the two `h`s get `synthetic` SourceInfo
   copied from their original positions.
4. The elaborator elaborates the expanded syntax and produces `TermInfo` nodes.
   The `TermInfo` for `dite` has synthetic SourceInfo. The `TermInfo` for `p`
   has synthetic SourceInfo.
5. `findReferences` skips all of these because none have `original` SourceInfo.
6. However, there will *also* be `TermInfo` nodes for the original syntax—the
   elaborator records info for both the macro invocation level and the expansion.
   The original `h`, `p`, etc. have `original` SourceInfo, so they *are*
   collected.

The end result is that references point to the positions the user actually wrote,
not to internal desugared forms.

### 6.3 The `canonical` flag: a middle ground

Sometimes macro-generated syntax *should* be visible to the user. The
`canonical` flag on `SourceInfo.synthetic` provides this middle ground. A
canonical synthetic position is one that should be treated "as if the user really
wrote it" for hovers and error messages.

However, for `findReferences` specifically, even canonical synthetic positions
are excluded—the filter checks for `.original`, not for "has a position."
This is intentional: the reference system wants to know exactly which positions
in the source text correspond to uses of a definition, and canonical synthetic
positions are still macro-generated positions, even if they happen to coincide
with user-written positions.

By contrast, the hover system (`Info.range?`) uses `canonicalOnly := true`,
which accepts both `.original` and `.synthetic (canonical := true)`. This means
hovers work on both user-written syntax and canonical macro outputs, providing
type information even for synthetic nodes that correspond to user intent.

### 6.4 Combining identifiers across expansion boundaries

The `combineIdents` function (`src/Lean/Server/References.lean:287`) handles
another macro-related complication. A single user-visible binding can correspond
to multiple internal identifiers:

- A `where` clause defines both an `FVar` (for use within the function body) and
  a top-level constant. Both have the same source range.
- `do`-reassignment (`x := e`) creates helper definitions.
- `match` generalization renames variables, connected by `FVarAliasInfo`.

`combineIdents` uses a union-find approach: definitions at the same range are
merged, and `FVarAliasInfo` nodes provide explicit alias information. When
merging, it prefers `RefIdent.const` over `RefIdent.fvar` as the canonical
representative, since constants are the globally-visible form.

### 6.5 What about `MacroExpansionInfo`?

When a macro is expanded, the elaborator records a `MacroExpansionInfo` node in
the InfoTree (`src/Lean/Elab/InfoTree/Types.lean:157`):

```lean
structure MacroExpansionInfo where
  lctx   : LocalContext
  stx    : Syntax      -- the original macro invocation
  output : Syntax      -- the expanded result
```

This node is pushed via `withMacroExpansionInfo`
(`src/Lean/Elab/InfoTree/Main.lean:485`) and becomes the parent of all info
nodes produced by elaborating the expansion. This means the InfoTree records
the full expansion chain.

However, `MacroExpansionInfo` is **not used by the "go to references" service
at all**. The `identOf` function (`src/Lean/Server/References.lean:241`) only
matches `Info.ofTermInfo`, `Info.ofFieldInfo`, `Info.ofOptionInfo`, and
`Info.ofDocElabInfo`—it ignores `Info.ofMacroExpansionInfo` entirely. The
`MacroExpansionInfo` nodes are simply traversed through by `visitM'` on the way
to the child `TermInfo` nodes that carry the actual semantic data.

`MacroExpansionInfo` is used by **other** parts of the system:

- **Linters** (`src/Lean/Linter/Util.lean`): The `collectMacroExpansions?`
  function walks up the InfoTree from a given range, collecting
  `MacroExpansionInfo` nodes on the way. This is used by the unused variable
  linter (`src/Lean/Linter/UnusedVariables.lean:542`) to understand whether a
  seemingly-unused variable was introduced by macro expansion, and therefore
  should not be flagged.

- **Tactic state display** (`src/Lean/Server/InfoUtils.lean:485`): When
  searching for nested tactics, the `hasNestedTactic` function descends through
  `MacroExpansionInfo` nodes transparently, treating them as structurally
  invisible wrappers.

- **Go to definition via custom elaborators** (`tests/lean/interactive/goTo.lean:41`):
  A custom term elaborator can call `withMacroExpansionInfo orig stx` to connect
  its output syntax back to the original syntax. This allows "go to declaration"
  on the macro invocation to navigate to the definition of the macro *syntax*
  itself rather than to the expanded form—a different LSP operation from
  "go to references."

So `MacroExpansionInfo` serves the InfoTree as a general-purpose record of the
expansion provenance, but the references system bypasses it entirely by relying
on the `.original` SourceInfo filter instead.

## 7. Summary: the data flow end to end

```
 User writes source code
   │
   ▼
 Parser produces Syntax with SourceInfo.original
   │
   ▼
 Macro expansion: macros transform syntax
   ├─ MacroExpansionInfo recorded in InfoTree (before/after)
   └─ Expanded syntax gets SourceInfo.synthetic
       │
       ▼
 Elaborator processes expanded syntax
   ├─ TermInfo, TacticInfo, etc. recorded in InfoTree
   ├─ Each Info carries the Syntax it was elaborated from
   └─ FVarAliasInfo recorded for variable renaming
       │
       ▼
 findModuleRefs extracts references from InfoTree
   ├─ findReferences: traverse InfoTree, filter for .original SourceInfo
   ├─ combineIdents: merge equivalent identifiers via range overlap + FVarAliasInfo
   └─ dedupReferences: group by (identifier, range)
       │
       ▼
 File worker sends ModuleRefs to watchdog via notifications
   ├─ $/lean/ileanInfoUpdate (incremental)
   └─ $/lean/ileanInfoFinal (complete)
       │
       ▼
 Watchdog aggregates References from workers + .ilean files
   │
   ▼
 textDocument/references request arrives
   ├─ findAt: find RefIdents at cursor position
   ├─ referringTo: collect all references across all modules
   └─ Return array of Locations to editor
```

## 8. Key source files

| File | Role |
|------|------|
| `src/Lean/Elab/InfoTree/Types.lean` | `InfoTree`, `Info`, `InfoState`, `MacroExpansionInfo` definitions |
| `src/Lean/Elab/InfoTree/Main.lean` | `pushInfoLeaf`, `withInfoContext`, `withMacroExpansionInfo` |
| `src/Lean/Server/InfoUtils.lean` | `InfoTree.visitM`, `Info.range?`, `Info.pos?` |
| `src/Lean/Server/References.lean` | `Reference`, `RefInfo`, `ModuleRefs`, `References`, `findReferences`, `findModuleRefs`, `combineIdents`, `referringTo` |
| `src/Lean/Server/FileWorker.lean` | `reportSnapshots`, ilean notification construction |
| `src/Lean/Server/Watchdog.lean` | `handleReference`, `References` aggregation |
| `Init/Prelude.lean` | `SourceInfo`, `SourceInfo.getPos?`, `SourceInfo.fromRef` |
