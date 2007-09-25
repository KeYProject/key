class C {
    C a;
    int i ;
    /* @ normalbehavior
       @         requires true ;       
       @      assignable a, i ;
       @      ensures a==null && i==1;
       @*/
          C( ) { a = null ; i = 1 ; }
}


class Alias {
    /* @ normalbehavior
       @          requires true ;
       @      assignable \nothing;
       @            ensures \result == 4;
       @ */
    int m() {
	C c = new C ( ) ;
	c.a = c;
	c.i = 2;
	return c.i + c.a.i;
    }
}

