// this is the HELPER model for CASHMO
module cashmo

open util/ordering[State] as ord

// an account has a value
abstract sig Value{}

// an account is held by a Person
abstract sig Account{
	value: set Value
}

abstract sig Person{
	account: set Account,
	bank: set Account,
	card: set Account
}

// there are two people in the model who each olds an account with a value
one sig Person1, Person2 extends Person{}
one sig Account1, Account2 extends Account{}
one sig Bank1, Bank2 extends Account{}
one sig Card1, Card2 extends Account{}
one sig AVal1, AVal2, BVal1, BVal2, CVal1, CVal2 extends Value{}

// each person has a cashmo account, bank account, and a credit/debit card
fact { account = Person1 -> Account1 && bank = Person1 -> Bank1 && card = Person1 -> Card1 }
fact { account = Person2 -> Account2 && bank = Person2 -> Bank2 && card = Person2 -> Card2 }
fact { value = Account1 -> AVal1 && value = Bank1 -> BVal1 && value = Card1 -> CVal1}
fact { value = Account2 -> AVal2 && value = Bank2 -> BVal2 && value = Card2 -> CVal2}

sig State{
	empty: set Value,
	full: set Value
}

// each cashmo account starts with an empty value and each bank and card starts with a full value
fact initialState{
	let s0 = ord/first |  (s0.empty = Account1.value && s0.empty = Account2.value) && 
					(s0.full = Bank1.value && s0.full = Bank2.value) &&
					(s0.full = Card1.value && s0.full = Card2.value)
}

// FOR FUTURE IMPLEMENTATION
//
//pred hasFullAmount [oldValue, newValue] {
//	newValue = oldValue
//}
//
//fact stateTransition1{
//	all s: State, t: ord/next[s]
	//Account in s.empty =>
		//hasFullAmount[s.empty, s.full]
//}

pred Show{}

pred terminatingState { ord/last.empty = Value}

run Show for 2 Person
