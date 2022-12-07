// this is the model for CASHMO
module cashmo

open util/ordering[State] as ord

sig Client{
	account: one Cashmo,
	bank: some Bank
}

abstract sig Account{
	owner: one Client
}

sig Cashmo extends Account{}
sig Bank extends Account{}

sig State{
	empty: some Account,
	full: some Account,
	sufficient: some Account,
	notSufficient: some Account
}

// each client has their own unique bank and Cashmo account
fact eachHasOneOfEach{
	all c : Client | 
	( c.account.owner = c && c.bank.owner = c) && ( c = c.account.owner && c = c.bank.owner)
}

// ensuring that each bank or Cashmo accounts cannot be sufficient AND not sufficient at the same state
// and that if the cashmo account or the bank account is empty, then it cannot be sufficient
fact eitherSufficientOrNotSufficient{
	no c : Client, s: State.sufficient, n: State.notSufficient |
	(c.account = s iff c.account = n) and (c.bank = s iff c.bank = n)
}

fact notEmptyAndSufficient{
	no c : Client, e: State.empty, s: State.sufficient |
	( c.account = e iff c.account = s ) and ( c.bank = e iff c.bank = s )
}

fact allAccountsHaveAState{
	all s : State, a: Cashmo, b: Bank |
	( a = s.empty or a = s.full ) implies ( b = s.empty or b = s.full )
}

// ensuring that a bank or Cashmo account cannot be empty AND full at the same State
fact eitherFullOrEmpty{
	no e : State.empty, f : State.full, c : Client |
	( c.account = e iff c.account = f) and ( c.bank = e iff c.bank = f)
}

assert clientExists{
	all c: Client | c = lookupClient[c]
}
//check clientExists for 1 Client

assert clientHasCashmo{
	all c: Client | c.account = lookupCashmo[c]
}
//check clientHasCashmo for 1 Client

assert clientHasUnsatisfiableCashmoAtStart{
	no c: Client |
	c.account = lookupCashmoSatisfiability[c.account]
}
//check clientHasUnsatisfiableCashmoAtStart for 15 Client, 30 Account, 1 State

assert clientHasSatisfiableBankAtStart{
	all c: Client |
	c.bank = lookupBankSatisfiability[c]
}
//check clientHasEmptyCashmoAtStart for 1 Client, 15 Account, 1 State

// find a client
fun lookupClient [c: Client]: lone Client{
	c & Client
}

// find the cashmo of that a client owns
fun lookupCashmo [c: Client]: one Cashmo{
	c.account & Cashmo
}

// find the satisfiability of a cashmo
fun lookupCashmoSatisfiability [a: Cashmo]: lone Cashmo{
	a & State.sufficient
}

// find the satisfiable banks a client owns
fun lookupBankSatisfiability [c: Client]: set Bank{
	c.bank & State.sufficient
}

// //transfer funds from bank
pred transferFromBank[t: Cashmo, f: Bank, s: State] {
	t = s.full and f = s.empty
}

 //transfer funds to bank
pred transferToBank[t: Bank, f: Cashmo, s: State] {
	t = s.full and f = s.empty
}

 //transfer funds to client
pred transferToClient[f: Client, t : Client, s: State] {
	lookupCashmo[t] = s.full and
	lookupCashmo[f] = s.empty
}

pred show{}

run show for exactly 2 Client, 6 Account, 2 State, 2 Cashmo


















