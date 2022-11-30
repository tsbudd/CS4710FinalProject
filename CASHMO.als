// this is the model for CASHMO
module cashmo

open util/ordering[State] as ord

sig Client{
	account: lone Cashmo,
	bank: lone Bank
}

abstract sig Account{
	owner: set Client
}

sig Cashmo extends Account{}
sig Bank extends Account{}

sig State{
	empty: set Account,
	full: set Account,
	sufficient: set Account,
	notSufficient: set Account
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
	no c : Client, e: State.empty, s: State.sufficient, n: State.notSufficient |
	( c.account = e && c.account = s ) && (c.account = s && c.account = n)
	&& ( c.bank = e && c.bank = s ) && (c.bank = s && c.bank = n)
}

// ensuring that a bank or Cashmo account cannot be empty AND full at the same State
fact eitherFullOrEmpty{
	no e : State.empty, f : State.full, c : Client |
	( c.account = e && c.account = f)
	&& ( c.bank = e && c.bank = f)
}

pred show{}

run show for exactly 2 Client, 4 Account, 2 State































