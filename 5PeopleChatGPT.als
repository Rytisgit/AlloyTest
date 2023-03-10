sig Person {
color:  disj one Color,
position: disj  one Position,
pet: disj one Pet,
drink: disj  one Drink,
smoke:  disj one Smoke,
nextTo: set Position,
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
fact "Person is not next  to himself" {
	all p:Person | no p.position & p.nextTo
}
fact "cant have no difference between next to" {
 all p1, p2: Person | p1!=p2 =>{
	some (p1.nextTo - p2.nextTo) + (p2.nextTo - p1.nextTo)
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
	 #p.leftOf = 2 && One in p.leftOf && Two in p.leftOf
}
 all p : Person | p.position = Four =>{
	 #p.leftOf = 3 && One in p.leftOf && Two in p.leftOf && Three in p.leftOf
}
 all p : Person | p.position = Five =>{
	 #p.leftOf = 4 && One in p.leftOf && Two in p.leftOf && Three in p.leftOf && Four in p.leftOf
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

pred GPTAnswer {
	all p: German | p.drink=Water
	all p: Person | p.smoke = Dunhill => p.color = Yellow
	all p1:Person , p2 : German | p1.smoke = BlueMaster => p2.position in p1.nextTo
}
run GPTAnswer for 4 but 4 int, 4 seq expect 1

run {} for 4 but 4 int, 4 seq expect 1
