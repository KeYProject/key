public class NestedAnonymousClasses{

    /*@ public normal_behavior
      @  ensures true;
      @*/
    public void nest(){
	final Executer e1 = new Executer();
	final Executer e2 = new Executer();
	e1.execute(new Runnable(){
		public void run(){
		    final Executer e3 = new Executer();
		    e2.execute(new Runnable(){
			    public void run(){
				e2.execute(new Runnable(){
					public void run(){
					    e1.execute(new Runnable(){
						    public void run(){
							e3.execute(new Runnable(){
								public void run(){}
							    }
							    );
						    }
						}
						);
					}
				    }
				    );
			    }
			}
			);
		}
	    });
    }


    class Executer{
	
	void execute(Runnable r){
	    r.run();
	}

    }

}