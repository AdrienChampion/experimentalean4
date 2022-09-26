import Csm.Init
import Csm.Opened
import Csm.Closed



/-! # A dumb state to make sure things work as intended -/

namespace Example



/-- Opaque [`Nat`] container. -/
structure Money where
  private amount : Nat
deriving BEq, Repr

instance instToStringMoney : ToString Money where
  toString :=
    (toString ·.amount)

instance instAddMoney : HAdd Money Money Money where
  hAdd l r :=
    ⟨l.amount + r.amount⟩


/-- Opaque account balance.

Can be negative, but once it is negative withdrawals are rejected.
-/
structure Account where
private innerMk ::
  private balance : Int
deriving BEq, Repr

instance instToStringAccount : ToString Account where
  toString :=
    (toString ·.balance)

namespace Account
  variable
    (self : Account)

  def mk (balance : Nat) : Account where
    balance := balance

  def deposit
    (money : Money)
  : Account where
    balance :=
      self.balance + money.amount

  def withdraw
    (n : Nat)
  : Res (Money × Account) :=
    if self.balance > 0 then
      let balance :=
        ⟨self.balance - n⟩
      pure (⟨n⟩, balance)
    else
      let msg :=
        s!"your balance is negative (`{self.balance}`), cannot withdraw money (`{n}`)"
      Res.bail msg

  def getBalance : Int :=
    self.balance
end Account


/-- Monadic money-related operations. -/
class MoneyIsDumb
  (μ : (Type → Type) → Type → Type)
where
  deposit
    {m : Type → Type}
    [Monad m]
    (money : Money)
  : μ m Unit
  withdraw
    (amount : Nat)
  : μ Res Money
  balance
    {m : Type → Type}
    [Monad m]
  : μ m Int

export MoneyIsDumb (deposit withdraw balance)



section opened
  protected abbrev Account.OsmT :=
    OsmT Account
  protected abbrev Account.EOsm :=
    EOsm Account
  protected abbrev Account.Osm :=
    Osm Account

  /-- Money operations for the open version. -/
  instance instMoneyIsDumbOsm
  : MoneyIsDumb Account.OsmT where

    deposit
      {m : Type → Type}
      [Monad m]
      (money : Money)
    : Account.OsmT m Unit :=
      fun s =>
        let s := s.deposit money
        pure ((), s)

    withdraw
      (amount : Nat)
    : Account.EOsm Money :=
      fun s => s.withdraw amount

    balance
      {m : Type → Type}
      [Monad m]
    : Account.OsmT m Int :=
      fun s => pure (s.getBalance, s)

  def Account.Osm.deposit
    {m : Type → Type}
    [Monad m]
  : Money → Account.OsmT m Unit :=
    instMoneyIsDumbOsm.deposit
  def Account.EOsm.withdraw :=
    instMoneyIsDumbOsm.withdraw
  def Account.EOsm.balance
    {m : Type → Type}
    [Monad m]
  : Account.OsmT m Int :=
    instMoneyIsDumbOsm.balance
end opened



section closed
  protected abbrev Account.CsmT :=
    CsmT Account
  protected abbrev Account.ECsm :=
    ECsm Account
  protected abbrev Account.Csm :=
    Csm Account

  /-- Money operations for the open version. -/
  instance instMoneyIsDumbCsm
  : MoneyIsDumb Account.CsmT where
    deposit
      {m : Type → Type}
      [Monad m]
      (money : Money)
    : Account.CsmT m Unit :=
      CsmT.stateDo
        fun s => s.deposit money

    withdraw
      (amount : Nat)
    : Account.ECsm Money :=
      CsmT.stateYield
        fun s => s.withdraw amount
    
    balance
      {m : Type → Type}
      [Monad m]
    : Account.CsmT m Int :=
      ⟨Account.EOsm.balance⟩

  def Account.Csm.deposit
    {m : Type → Type}
    [Monad m]
  : Money → Account.CsmT m Unit :=
    instMoneyIsDumbCsm.deposit
  def Account.ECsm.withdraw :=
    instMoneyIsDumbCsm.withdraw
  def Account.ECsm.balance
    {m : Type → Type}
    [Monad m]
  : Account.CsmT m Int :=
    instMoneyIsDumbCsm.balance
end closed
