public interface Observer {
    
    //@ public instance model Subject subject;
    //@ public instance model boolean upToDate;
    
    //@ depends \inv: this.*;    
    //@ depends subject: this.*;
    //@ depends upToDate: \set_union(this.*, subject.footprint); 
        
    /*@ public normal_behaviour
      @   requires subject.\inv && \disjoint(subject.footprint, this.*);
      @   assignable this.*;
      @   ensures upToDate;
      @   ensures subject == \old(subject);
      @*/
    public void update();
}
