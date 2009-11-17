//Examples from the paper 
//"Abstract Interpretation of Symbolic Execution with Explicit State Updates"

class UpdateAbstraction {
    
    static int l;
    static int l2;    
    static int h;
    
    //@ static model \set LOW;           	//just an abbreviation
    //@ static represents LOW <- \setUnion(l, l2);
    //@ static model \set HIGH;           	//just an abbreviation
    //@ static represents HIGH <- \singleton(h);
    
    //@ static ghost \set pcDep;     //buffer for dependencies of program counter     
    
    //@ static ghost \set lDep;  //one dep field for every normal field
    //@ static ghost \set l2Dep; //one dep field for every normal field    
    //@ static ghost \set hDep;  //one dep field for every normal field
    
    
    /*@ requires pcDep == \empty;
      @ requires lDep == \singleton(l);
      @ requires l2Dep == \singleton(l2); 
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_1_insecure() {
	//@ set lDep = \setUnion(pcDep, hDep); //assignment
	l = h;
    }
    
    
    /*@ requires pcDep == \empty;
      @ requires lDep == \singleton(l); 
      @ requires l2Dep == \singleton(l2);      
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_2_insecure() {
	//@ set pcDep = \setUnion(pcDep, hDep); //entering conditional
	if(h > 0) {
	    //@ set lDep = pcDep; //assignment 
	    l = 1;
	} else {
	    //@ set lDep = pcDep; //assignment
	    l = 2;
	}
    }
    
    
    /*@ requires pcDep == \empty;
      @ requires lDep == \singleton(l); 
      @ requires l2Dep == \singleton(l2);      
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_3_secure() {
	//@ set pcDep = \setUnion(pcDep, hDep); //entering conditional
	if(l > 0) {
	    //@ set hDep = pcDep; //assignment 
	    h = 1;
	} else {
	    //@ set hDep = pcDep; //assignment
	    h = 2;
	}
    }   
    
    
    /*@ requires pcDep == \empty;
      @ requires lDep == \singleton(l); 
      @ requires l2Dep == \singleton(l2);      
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_4_secure() {
	//@ ghost \set oldPcDep = pcDep;         //entering conditional
	//@ set pcDep = \setUnion(pcDep, hDep); //entering conditional
	if(h > 0) {
	    //@ set hDep = pcDep; //assignment 
	    l = 1;
	} else {
	    //@ set hDep = pcDep; //assignment
	    l = 2;
	}
	//@ set pcDep = oldPcDep; //leaving conditional; setting back pcDep is allowed because conditional has no other exit points
	
	//@ set lDep = pcDep; //assignment
	l = 3;
    }     
    
    
    /*@ requires pcDep == \empty;
      @ requires lDep == \singleton(l);
      @ requires l2Dep == \singleton(l2);       
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_5_secure() {
	//@ set hDep = pcDep; //assignment
	h = 0;
	
	//@ set lDep = \setUnion(pcDep, hDep); 
	l = h;
    } 
    
    
    //different encoding here (following the paper more closely)    
    /*@ requires lDep == \singleton(l); 
      @ requires l2Dep == \singleton(l2); 
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_6_secure() {
	//ghost code for entering conditional----->
	//@ ghost \set guardDep = hDep;
	int lOld = l;	
	int hOld = h;
	//<----------------------------------------
	
	if(h > 0) {
	    //@ set hDep = lDep; //assignment
	    h = l;
	    //@ set lDep = hDep; //assignment
	    l = h;
	}
	
	//ghost code for leaving conditional------>
	if(l != lOld) {
	    //@ set lDep = \setUnion(lDep, guardDep);
	    ;
	}
	if(h != hOld) {
	    //@ set hDep = \setUnion(hDep, guardDep);
	    ;
	}
	//<-----------------------------------------
    }        
    
    
    //again the encoding of 7_6 (cannot prove security)
    /*@ requires lDep == \singleton(l);
      @ requires l2Dep == \singleton(l2);     
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_7_secure() {
	//ghost code for entering conditional----->
	//@ ghost \set guardDep = hDep;
	int lOld = l;	
	int hOld = h;
	//<----------------------------------------	
	
	if(h > 0) {
	    //@ set lDep = \empty; //assignment
	    l = 2;	    
	    //@ set hDep = \empty; //assignment	    
	    h = 2;
	} else {
	    //@ set lDep = \empty; //assignment	    
	    l = 2;
	    //@ set hDep = \empty; //assignment	    
	    h = 2;
	}
	
	//ghost code for leaving conditional------>
	if(l != lOld) {
	    //@ set lDep = \setUnion(lDep, guardDep);
	    ;
	}
	if(h != hOld) {
	    //@ set hDep = \setUnion(hDep, guardDep);
	    ;
	}
	//<-----------------------------------------
    }         
    
    
    //again the encoding of 7_6 (cannot prove security)
    /*@ requires lDep == \singleton(l); 
      @ requires l2Dep == \singleton(l2); 
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_8_secure() {
	//@ set lDep = hDep; //assignment
	l = h - h;
    }         
    
    
    /*@ requires pcDep == \empty;
      @ requires lDep == \singleton(l);
      @ requires l2Dep == \singleton(l2);       
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/    
    static void ex9_secure() {
	//@ set lDep = pcDep; //assignment
	l = 0;
	//@ set l2Dep = pcDep; //assignment
	l2 = 0;
	
	//@ set pcDep = \setUnion(pcDep, hDep); //entering loop
	/*@ loop_invariant l2 >= 0;
	  @ assignable l2, \singleton(l2Dep), h, \singleton(hDep), \singleton(pcDep);
	  @*/
	while(h < 0) {
	    //@ set l2Dep = \setUnion(pcDep, l2Dep); //assignment
	    l2++;
	    //@ set hDep = \setUnion(pcDep, hDep);
	    h++;
	    //@ set pcDep = \setUnion(pcDep, hDep); //entering loop again	    
	}
	//@ set pcDep = \setUnion(pcDep, l2Dep); //entering conditional
	if(l2 < 0) {
	    //@ set lDep = pcDep; //assignment
	    l = 1;
	}
    }
}
