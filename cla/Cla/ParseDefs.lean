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


