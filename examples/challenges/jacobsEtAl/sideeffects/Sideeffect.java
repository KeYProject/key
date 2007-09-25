class Sideeffect {

    boolean b = true;
    boolean result1,result2;
    /* @normal_behavior
       @requires true;
       @assignable b;
       @ensures b==!\old(b) && \result==b;
       @
    */
    boolean f(){
	b = !b;
	return b;
    }
    
    /*@normal_behavior
      @         requires true ;
      @       assignable b , result1 , result2 ;
      @  ensures(\old(b)==>!result1 && result2)&&
      @ (!\old(b)==> result1 && result2);
      @*/
    void m () {    
	result1 = f() || !f() ; 
	result2 = !f() && f() ; 
    }    
}