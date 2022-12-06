// this is the model for CASHMO
module cashmoHelp

open util/ordering[State] as ord

sig Client{
	account: lone Cashmo,
	bank: some Bank
}

abstract sig Account{
	owner: set Client
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
	( c.account.owner = c && c.bank.owner = c)
}

// all external bank accounts are full and all Cashmo accounts are empty at start
// if an Account object is empty, it is not sufficient to transfer funds out of
fact initialState{
	let s0 = ord/first, c = Client | 
	( s0.empty = c.account && s0.full = c.bank && s0.sufficient = c.bank && s0.notSufficient = c.account)
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

// ensuring that a bank or Cashmo account cannot be empty AND full at the same State
fact eitherFullOrEmpty{
	no e : State.empty, f : State.full, c : Client |
	( c.account = e iff c.account = f) and ( c.bank = e iff c.bank = f)
}

// find the cashmo of that a person owns
fun lookupCashmo [c: Client]: set Cashmo{
	c.account & Cashmo
}

pred show{}

run show for  2 Client, 4 Account, 2 State
