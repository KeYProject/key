package loop;

public class IFLoopExamples {
	int low;

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void secure_noWhile(int x) {
		low = low + 1;
		x = x - 1;
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void secure_while(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void loc_secure_while(int x) {

		int z = 2;
		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x, z;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
			z = z + x;
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void secure_twoWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}

		/*@
		  @ loop_invariant x >= -1;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x+1;
		  @*/
		while (x == 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low;
	  @*/
	public void insecure_twoWhile_2(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}

		/*@
		  @ loop_invariant x >= -1;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x+1;
		  @*/
		while (x == 0) {
			low = low + 1;
			x = x - 1;
		}
	}

        /*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void insecure_twoWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}

		/*@
		  @ loop_invariant x >= -1;
		  @ assignable low;
		  @ separates x;
		  @ decreases x+1;
		  @*/
		while (x == 0) {
			low = low + 1;
			x = x - 1;
		}
	}

        /*@
	  @ requires    x >= 1;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void secure_while_wrongInv(int x) {

		/*@
		  @ loop_invariant x >= 1;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires    x >= 1;
	  @ assignable low;
	  @ separates    low;
	  @*/
	public void notSecure_while_wrongInv(int x) {

		/*@
		  @ loop_invariant x >= 1;
		  @ assignable low;
		  @ separates low;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low;
	  @*/
	public void notSecure_while(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void secure_nestedWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;
			
			/*@
			  @ loop_invariant x >= 0;
			  @ assignable low;
			  @ separates low, x;
			  @ decreases x;
			  @*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;				
			}
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void secure_nestedTwoWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;

			/*@
			  @ loop_invariant x >= 0;
			  @ assignable low;
			  @ separates low, x;
			  @ decreases x;
			  @*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;				
			}

			/*@
			  @ loop_invariant x >= 0;
			  @ assignable low;
			  @ separates low, x;
			  @ decreases x;
			  @*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;				
			}
		}
	}

	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void secure_doubleNestedWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;

			/*@
			@ loop_invariant x >= 0;
			@ assignable low;
			@ separates low, x;
			@ decreases x;
			@*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;

				/*@
				  @ loop_invariant x >= 0;
				  @ assignable low;
				  @ separates low, x;
				  @ decreases x;
				  @*/
				while (x > 0) {
					low = low + 1;
					x = x - 1;
				}				
			}
		}
	}

        	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low;
	  @*/
	public void insecure_doubleNestedWhile(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;

			/*@
			@ loop_invariant x >= 0;
			@ assignable low;
			@ separates low, x;
			@ decreases x;
			@*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;

				/*@
				  @ loop_invariant x >= 0;
				  @ assignable low;
				  @ separates low, x;
				  @ decreases x;
				  @*/
				while (x > 0) {
					low = low + 1;
					x = x - 1;
				}
			}
		}
	}

        	/*@
	  @ requires    x >= 0;
	  @ assignable low;
	  @ separates    low, x;
	  @*/
	public void insecure_doubleNestedWhile2(int x) {

		/*@
		  @ loop_invariant x >= 0;
		  @ assignable low;
		  @ separates low, x;
		  @ decreases x;
		  @*/
		while (x > 0) {
			low = low + 1;
			x = x - 1;

			/*@
			@ loop_invariant x >= 0;
			@ assignable low;
			@ separates low;
			@ decreases x;
			@*/
			while (x > 0) {
				low = low + 1;
				x = x - 1;

				/*@
				  @ loop_invariant x >= 0;
				  @ assignable low;
				  @ separates low, x;
				  @ decreases x;
				  @*/
				while (x > 0) {
					low = low + 1;
					x = x - 1;
				}
			}
		}
	}
        
        
                /*@
          @ requires   x >= 0;
          @ assignable low;
          @ separates   low, x;
          @*/
        public void secure_while_4(int x) {
                low = low + 1;
                /*@
                  @ loop_invariant 0 <= x;
                  @ assignable  low;
                  @ separates    low, x;
                  @ decreases   x;
                  @*/
                while (x > 0) {
                        low = low + 1;
                        x = x - 1;
                }
                low = low + 1;
        }

        /*@
          @ requires   x >= 0;
          @ assignable low;
          @ separates   low, x;
          @*/
        public void secure_while_2(int x) {
                low = low + 1;
                /*@
                  @ loop_invariant 0 <= x;
                  @ assignable  low;
                  @ separates    low, x;
                  @ decreases   x;
                  @*/
                while (x > 0) {
                        low = low + 1;
                        x = x - 1;
                }
                low = low + 1;
        }

        /*@
          @ requires   x >= 1;
          @ assignable low;
          @ separates   low;
          @*/
        public void secure_while_3(int x) {
                low = low + 1;
                /*@
                  @ loop_invariant 1 <= x;
                  @ assignable  low;
                  @ separates    low;
                  @ decreases   x;
                  @*/
                while (x > 0) {
                        low = low + 1;
                        x = x - 1;
                }
                low = low + 1;
        }

        /*@
          @ requires   x >= 0;
          @ assignable low;
          @ separates   low, x;
          @*/
        public void secure_no_while(int x) {
            low = low + 1;
            x = x - 1;
        }


        /*@
          @ requires   x >= 0;
          @ assignable low;
          @ separates   low, x;
          @*/
        public void secure_no_while_2(int x) {
            secure_no_while(x);
            secure_no_while(x);
        }

//        //@ separates \declassifies l \erases \result;  // separates l, \result;
//        public int m(int l) {
//            int l1 = l;
//
//            //@ separates l1;
//            {   l1++;
//            }
//
//            return l1;
//        }

        //@ normal_behavior
        //@ separates low;
        public void m(int secret) {
            int x = 0;
            int y = 0;
            //@ loop_invariant 0 <= y && y <= 10;
            //@ separates low, y, (y < 10 ? x : 0);
            //@ assignable low;
            //@ decreases 10 - y;
            while (y < 10) {
                print(x);
                if (y == 5) {
                    x = secret;
                    y = 9;
                }
                x++;
                y++;
            }
        }
        
        //@ normal_behavior
        //@ separates low, x;
        //@ assignable low;
        //@ helper
        public void print(int x) {
            low = x;
        }
}