import Csm.Init
import Csm
import Csm.Example

open Example

def runTest
  (state : Account)
  (test : Account.EOsm Money)
: IO Unit :=
  do
    println! "initial state `{state}`"
    let res := test.run state
    match res with
    | .ok (money, state) =>
      println! "success"
      println! "- final state `{state}`"
      println! "-       money `{money}`"
    | .error msg =>
      println! "failure: {msg}"



def test1 : Account.EOsm Money :=
  do
    let balance ←
      Account.EOsm.balance
    Account.EOsm.withdraw 666
    |>.context (𝕂 s!"with balance `{balance}`")

def test2 : Account.EOsm Money :=
  do
    let originalBalance ←
      Account.EOsm.balance
    let m₁ ←
      Account.EOsm.withdraw 17
      |>.context (fun _ => s!"with balance `{originalBalance}`")
    let balance ←
      Account.EOsm.balance
    let m₂ ←
      Account.EOsm.withdraw 666
      |>.context (fun _ => s!"with balance `{balance}`")
      |>.context (fun _ => s!"after withdrawing `{m₁}`")
      |>.context (fun _ => s!"from original balance `{originalBalance}`")
    return m₁ + m₂


def main : IO Unit :=
  let state :=
    Account.mk 10
  do
    println! "## Running test 1\n"
    runTest state test1
    println! "\n## Running test 2\n"
    runTest state test2
