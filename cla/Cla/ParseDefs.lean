import Cla.Com



namespace Cla



def Parse.flagArgs
  (argSpec : ArgSpec σ)
: IParseM (EStateM String σ Unit) :=
  ArgSpec.Bounds.MProdRun
    argSpec.bounds
    Parse.nextFlagArg
    (Parse.flagAllArgs argSpec.bounds.max)
    argSpec.validator

protected def Parse.shortOrLong
  (com : Com σ)
  (shortOrLong : Either String String)
  (state : σ)
: IParseM σ :=
  do
    let flag ←
      match shortOrLong with
      | .left short => com.shortOf short
      | .right long => com.longOf long
    let work ←
      Parse.flagArgs flag.args
    match work state with
    | .error e _ => throw e
    | .ok () state => pure state

def Parse.short
  (com : Com σ)
  (short : String)
: σ → IParseM σ :=
  Either.left short
  |> Parse.shortOrLong com

def Parse.long
  (com : Com σ)
  (long : String)
: σ → IParseM σ :=
  Either.right long
  |> Parse.shortOrLong com

def Parse.val
  (_com : Com σ)
  (_arg : String)
  (_idx : Nat)
: σ → IParseM σ :=
  fun _ =>
    do
      throw "plain values are not supported yet"

def Parse.com
  (com : Com σ)
  (state : σ)
: ParseM σ :=
  Parse.loopDo
    (longDo := fun state long => Parse.long com long state)
    (shortDo := fun state short => Parse.short com (toString short) state)
    (valDo := fun state val idx => (Parse.val com val idx state))
    (foldl := fun _old new => new)
    (init := state)

def Parse.run
  (com : Com σ)
  (init : σ)
  (args : List String)
: Except Parse.Err σ :=
  let parser :=
    Parse.mk args
  let run :=
    Parse.com com init
  do
    match run parser with
    | .ok conf parser =>
      match parser.remainingNonSep with
      | [] => pure conf
      | hd :: tl =>
        -- this is actually unreachable because parsing consumes
        -- all its arguments, **at the time I am writing this**
        let spurious :=
          tl.foldl
            (fun acc arg => s! "{acc} {arg}")
            s! "{hd}"
        throw
        <| Parse.Err.mk
          none
          s! "spurious remaining arguments after parsing: {spurious}"
        
    | .error err _ => throw err

