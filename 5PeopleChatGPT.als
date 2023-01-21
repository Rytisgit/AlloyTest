sig Person {
color:  disj one Color,
position: disj  one Position,
pet: disj one Pet,
drink: disj  one Drink,
smoke:  disj one Smoke,
nextTo: set Position,
notNextTo: set Position,
leftOf: set Position,
}
one sig Brit, Norwegian, German, Swede, Dane extends Person {}
enum Color { Red, Blue, Green,White,Yellow }
enum Position {One,Two,Three,Four,Five}
//5th pet didn't exist, adding None
enum Pet { Bird, Cat, Horse,Dog,None }
enum Drink { Water, Tea, Coffee, Beer,Milk }
enum Smoke { BlueMaster, PallMall, Blends,Dunhill,Prince }


fact "Person is next to 1 or 2 people" {
	all p:Person | #p.nextTo = 1 || #p.nextTo = 2
}
fact "Person is not next to 2 or 3 people" {
	all p:Person | #p.notNextTo = 2 || #p.notNextTo = 3
}
fact "Person is next or not next to all others" {
	all p:Person | #(p.nextTo + p.notNextTo) = 4
}
fact "Person is not next and notnotNext to himself" {
	all p:Person | no p.position & p.nextTo && no p.position & p.notNextTo
}
fact "Person cannot be next to and not next to  position"{
	all p:Person | p.nextTo & p.notNextTo = none
}
fact "cant have no difference between next to" {
 all p1, p2: Person | p1!=p2 =>{
	some (p1.nextTo - p2.nextTo) + (p2.nextTo - p1.nextTo)
}
}
fact "cant have no difference between not next to" {
 all p1, p2: Person | p1!=p2 =>{
	some (p1.notNextTo - p2.notNextTo) + (p2.notNextTo - p1.notNextTo)
}
}
fact "Position Nextness" {
 all p : Person | p.position = One =>{
	p.nextTo = {Two}
}
 all p : Person | p.position = Two =>{
	 One in p.nextTo &&  Three in p.nextTo 
}
 all p : Person | p.position = Three =>{
	 Two in p.nextTo &&  Four in p.nextTo 
}
 all p : Person | p.position = Four =>{
	 Five in p.nextTo &&  Three in p.nextTo 
}
 all p : Person | p.position = Five =>{
	p.nextTo = {Four}
}
}
fact "Position to the left of" {
 all p : Person | p.position = One =>{
	p.leftOf = none
}
 all p : Person | p.position = Two =>{
	 #p.leftOf = 1 && One in p.leftOf
}
 all p : Person | p.position = Three =>{
	 #p.leftOf = 1 && Two in p.leftOf
}
 all p : Person | p.position = Four =>{
	 #p.leftOf = 1 && Three in p.leftOf
}
 all p : Person | p.position = Five =>{
	 #p.leftOf = 1&& Four in p.leftOf
}
}

fact "The Brit lives in a red house" {
 all p : Brit | p.color = Red
}
fact "The Swede keeps dogs as pets" {
 all p : Swede | p.pet = Dog
}
fact "The Dane drinks tea" {
 all p : Dane | p.drink = Tea
}
fact "The Green house is on the left of the white house" { 
 all p1 : Person |  p1.color = White =>{ some p1.leftOf}
 all p1,p2 : Person |  p1.color = White && p2.color = Green => p2.position in p1.leftOf
}
fact "The Owner of the green house drink coffee" {
 all p : Person | p.color = Green => p.drink = Coffee
}
fact "The person who smokes Pall Mall rears birds" {
 all p : Person | p.smoke = PallMall => p.pet = Bird
}
fact "The Owner of the yellow house smokes Dunhill" {
 all p : Person | p.color = Yellow => p.smoke = Dunhill
}
fact "The man living in the center house drinks milk" {
 all p : Person | p.position = Three => p.drink = Milk
}
fact "The Norwegian lives in the first house" {
 all p : Norwegian | p.position = One
}
fact "The man who smokes Blends lives next to the one who keeps cats" {
 all p1,p2 : Person |  p1.smoke = Blends && p2.pet = Cat => p2.position in p1.nextTo
}
fact "The man who keeps horses lives next to the man who smokes Dunhill" {
 all p1,p2 : Person | p1.pet = Horse && p2.smoke = Dunhill => p2.position in p1.nextTo
}
fact "The man who smokes Blue Master drinks beer" {
 all p : Person | p.smoke = BlueMaster => p.drink = Beer
}
fact "The German smokes Prince" {
 all p : German | p.smoke = Prince
}
fact "The Norwegian lives next to the blue house" {
 all p1: Norwegian, p2 : Person |  p2.color = Blue => p2.position in p1.nextTo
}
fact "The man who smokes Blends has a neighbor who drinks water" {
 all p1,p2 : Person | p1.smoke = Blends && p2.drink = Water => p2.position in p1.nextTo
}

run {} for 4 but 4 int, 4 seq expect 1
