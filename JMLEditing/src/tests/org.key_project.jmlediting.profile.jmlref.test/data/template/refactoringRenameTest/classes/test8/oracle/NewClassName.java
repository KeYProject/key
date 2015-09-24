package test;

public class NewClassName {
    
    /*@
      @ normal_behavior
      @ ensures \result == (NewClassName) someClass;
      @*/
    NewClassName castToTestClass(Object someClass) {
        if (someClass instanceof NewClassName){
            return (NewClassName) someClass;
        }
        else {
            return null;
        }
    }
}