class AbruptTermination {
   int[] ia;
    /* @ normalbehavior
       @           requires ia != null ;
       @       assignable ia[];
       @             ensures \forall int i; 0<=i && i<ia.length ==>
       @                   (\old ( ia[i]) < 0 &&
       @                   ( // i is the first position with negative value
       @                     \forall int j; 0 <= j && j<i ==> \old(ia[j]) >= 0 ) )
       @                   ? ( ia[i] == -\old ( ia[i] ) )
       @                   : ( ia[i] == \old ( ia[i] ) ) ;
       @ */

   void negatefirst() {
       /* @ maintaining i >= 0 &&  i < = ia.length &&
	  @ ( \forall int j; 0<=j && j<i ==>
	  @
	  @ ( ia[j] >= 0 && ia[j] == \old ( ia [j] ) ) ) ;
	  @ decreasing ia.length - i ;
	  @*/
         for (int i = 0 ; i < ia.length; i++) {
                 if ( ia[i] < 0 ) { ia [i] = -ia[i] ; 
		     break ; 
		 } 
	 }
   }
}
