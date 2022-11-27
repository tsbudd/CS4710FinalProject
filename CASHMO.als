// this is the model for CASHMO
module cashmo

open util/ordering[State] as ord

// an account has a value
abstract sig Value{}

// an account is held by a Person
abstract sig Account{
	value: set Value
}

abstract sig Person{
	holds: set Account
}

// there are two people in the model who each olds an account with a value
one sig Person1, Person2 extends Person{}
one sig Account1, Account2 extends Account{}
one sig Value1, Value2 extends Value{}

fact { holds = Person1 -> Account1}
fact { holds = Person2 -> Account2}
fact { value = Account1 -> Value1}
fact { value = Account2 -> Value2}

sig State{
	empty: set Value,
	full: set Value
}

// each account starts with an empty value
fact initialState{
	let s0 = ord/first |  (s0.empty = Account1.value && s0.empty = Account2.value) && no s0.full
}

//fact nextState{
//	let s1 = ord/second | (s1.full = Account1.value || s1.full = Account2.value)
//}


pred hasFullAmount [oldValue, newValue] {
	newValue = oldValue
}

fact stateTransition1{
	all s: State, t: ord/next[s]
	Account in s.empty =>
		hasFullAmount[s.empty, s.full]
}

pred terminatingState { ord/last.full = Account}

run terminatingState for 2 State expect 1
































