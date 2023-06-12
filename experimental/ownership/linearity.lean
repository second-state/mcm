import Mathlib.Data.List.Defs
import Lean.Data.HashMap

inductive Track
  | own
  | borrow
  | dead
deriving Repr

-- using mode
structure Mode where
  -- put smaller to left
  prior : Nat
  move : Track → Except String Track

def move : Mode := ⟨ 0, fn ⟩
  where
  fn : Track → Except String Track
  | .own => return .dead
  | track => throw s!"move from {repr track}"
def borrow : Mode := ⟨ 1, fn ⟩
  where
  fn : Track → Except String Track
  | .own => return .own
  | .borrow => return .borrow
  | track => throw s!"borrow from {repr track}"

-- only consider simplest case variable, since ownership is only for resource
inductive Expr
  | var (name : String) (mode : Mode)

inductive Statement
  | declare (var : String) (state : Track)
  | funcall (es : List Expr)

@[reducible]
def Prog := List Statement

@[reducible]
def TrackContext := Lean.HashMap String Track
instance : ToString TrackContext where
  toString ctx := toString <| ctx.toList.map (λ (k, v) => s!"{repr k} : {repr v}")

def TrackContext.lookup [Monad m] [MonadExcept String m]
  (ctx : TrackContext) (name : String) : m Track :=
  match ctx.find? name with
  | none => throw s!"variable `{name}` isn't get tracked"
  | some track => return track

def run [Monad m] [MonadStateOf TrackContext m] [MonadExcept String m] : Prog → m Unit
  | [] => return ()
  | .declare name init :: rest => do
    let ctx ← get
    set (ctx.insert name init)
    run rest
  | .funcall es :: rest => do
    let us := es.map (fun | .var name mode => (mode, name)) |> List.toArray
    let us := us.qsort (fun (a, _) (b, _) => a.prior < b.prior)
    for (mode, name) in us do
      let ctx ← get
      let track ← ctx.lookup name
      match mode.move track with
      | .ok t => set (ctx.insert name t)
      | .error ε => throw s!"invalid use: {ε}"
    run rest

def check (prog : Prog) : Except String TrackContext :=
  let M := StateT TrackContext (Except String)
  match run prog (m := M) {} with
  | .ok (_, s) => .ok s
  | .error e => .error e

notation "decl" x ":" t => Statement.declare x t 
notation "call" x => Statement.funcall x

-- one cannot move a value twice
#eval check [
  decl "x" : .own,
  call [(.var "x" move)],
  call [(.var "x" move)]
  ]
-- one cannot move from a borrowed value
#eval check [
  decl "x" : .borrow,
  call [(.var "x" move)]
  ]
-- moved variable is dead
#eval check [
  decl "x" : .own,
  call [(.var "x" move)],
  call [(.var "x" borrow)]
  ]
-- This is an interesting case, it shows borrow checker have to treat each use of a function call as parallel.
#eval check [
  decl "x" : .own,
  call [ (.var "x" borrow), (.var "x" move) ]
  ]

#eval check [
  decl "x" : .own,
  call [ (.var "x" borrow), (.var "x" borrow) ]
  ]
#eval check [
  decl "x" : .borrow,
  call [ (.var "x" borrow), (.var "x" borrow) ]
  ]
#eval check [
  decl "x" : .borrow,
  call [ (.var "x" borrow) ]
  ]
