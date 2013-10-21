package packageA;

import interfaces.MyInterface;

public interface InterfaceContainer {
   class DefaultChildClass {
      private int x;
      
      public DefaultChildClass(int x) {
         this.x = x;
      }
      
      public void run() {
         new MyInterface() {
         };
      }
   }
	
   public final class PublicChildClass {
      public class InnerInnerClass {
         public void innerInnerRun() {
            new MyInterface() {
            };
         }
      }
   }
   
   interface DefaultChildInterface {
      public interface InnerInnerInterface {
      }
      
      public class InnerInnerClass {
         public void innerInnerRun() {
            new MyInterface() {
            };
         }
      }
   }
	
   public abstract interface PublicChildInterface {
   }
   
   
   
   
   enum DefaultChildEnum {
      INSTANCE(42);
      
      private int x;
      
      private DefaultChildEnum(int x) {
         this.x = x;
      }
      
      public void run() {
         new MyInterface() {
         };
      }
   }
   
   public enum PublicChildEnum {
      INSTANCE;
      
//    public enum InnerInnerEnum {
//       INSTANCE;
//       
//       public void innerInnerRun() {
//          new MyInterface() {
//          };
//       }
//    }
   }
}