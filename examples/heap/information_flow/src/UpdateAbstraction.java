//Examples from the paper 
//"Abstract Interpretation of Symbolic Execution with Explicit State Updates"

class UpdateAbstraction {
    
    static int l;
    static int l2;    
    static int h;
    
    //@ static model \locset LOW;           	//just an abbreviation
    //@ static represents LOW = \set_union(l, l2);
    //@ static model \locset HIGH;           	//just an abbreviation
    //@ static represents HIGH = \singleton(h);
    
    //@ static ghost \locset pcDep;     //buffer for dependencies of program counter     
    
    //@ static ghost \locset lDep;  //one dep field for every normal field
    //@ static ghost \locset l2Dep; //one dep field for every normal field    
    //@ static ghost \locset hDep;  //one dep field for every normal field
    
    
    /*@ requires pcDep == \empty;
      @ requires lDep == \singleton(l);
      @ requires l2Dep == \singleton(l2); 
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_1_insecure() {
	//@ set lDep = \set_union(pcDep, hDep); //assignment
	l = h;
    }
    
    
    /*@ requires pcDep == \empty;
      @ requires lDep == \singleton(l); 
      @ requires l2Dep == \singleton(l2);      
      @ requires hDep == \singleton(h);
      @ ensures \subset(lDep, LOW);
      @*/
    static void ex7_2_insecure() {
	//@ set pcDep = \set_union(pcDep, hDep); //entering conditional
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
	//@ set pcDep = \set_union(pcDep, hDep); //entering conditional
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
	//@ ghost \locset oldPcDep = pcDep;         //entering conditional
	//@ set pcDep = \set_union(pcDep, hDep); //entering conditional
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
	
	//@ set lDep = \set_union(pcDep, hDep); 
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
	//@ ghost \locset guardDep = hDep;
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
	    //@ set lDep = \set_union(lDep, guardDep);
	    ;
	}
	if(h != hOld) {
	    //@ set hDep = \set_union(hDep, guardDep);
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
	//@ ghost \locset guardDep = hDep;
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
	    //@ set lDep = \set_union(lDep, guardDep);
	    ;
	}
	if(h != hOld) {
	    //@ set hDep = \set_union(hDep, guardDep);
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
      @ diverges true;
      @*/    
    static void ex9_secure() {
	//@ set lDep = pcDep; //assignment
	l = 0;
	//@ set l2Dep = pcDep; //assignment
	l2 = 0;
	
	//@ set pcDep = \set_union(pcDep, hDep); //entering loop
	/*@ loop_invariant l2 >= 0;
	  @ assignable l2, \singleton(l2Dep), h, \singleton(hDep), \singleton(pcDep);
	  @*/
	while(h < 0) {
	    //@ set l2Dep = \set_union(pcDep, l2Dep); //assignment
	    l2++;
	    //@ set hDep = \set_union(pcDep, hDep);
	    h++;
	    //@ set pcDep = \set_union(pcDep, hDep); //entering loop again	    
	}
	//@ set pcDep = \set_union(pcDep, l2Dep); //entering conditional
	if(l2 < 0) {
	    //@ set lDep = pcDep; //assignment
	    l = 1;
	}
    }
}
