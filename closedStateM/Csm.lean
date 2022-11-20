import Csm.Init
import Csm.Opened
import Csm.Closed
import Csm.Applied
import Csm.Example



open Example (Account)

structure State where
  accounts: Array Account

namespace State
  def empty : State where
    accounts := Array.empty

  variable
    (self : State)

  def new_account : Nat × State :=
    let n := self.accounts.size
    let self := ⟨self.accounts.push <| Account.mk 100⟩
    (n, self)

  def get (idx : Nat) : Account :=
    self.accounts.get! idx
end State

