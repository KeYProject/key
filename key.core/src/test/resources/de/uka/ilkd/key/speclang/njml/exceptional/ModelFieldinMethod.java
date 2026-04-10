// verbose: true
// broken: false
// exceptionClass: BuildingException
// msgContains: Model modifier on variable declaration detected, only model fields are allowed
// position: 11/19

class ModelFieldinMethod {

    int m() {

        /*@ model int modelMethod; */
        
        return 0;
    }
}


// Minssing position information :(
