
public class BranchStatementBlockTest {
   public static int recursiveMain() {
      return recursiveDecrease(3);
   }
   
   public static int recursiveDecrease(int x) {
      if (x > 0) {
         return recursiveDecrease(x - 1);
      }
      else {
         return x;
      }
   }
   
   public static int onlyEmptyThen() {
      if (2 == 2) {
      }
      return 42;
   }
   
   public static int switchTest(int x) {
      switch (x) {
      case 1 : {return 1;}
      case 2 : 
      case 3 : return 23;
      case 4 : int helper4 = 4; return helper4;
      case 5 : {int helper5 = 5; return helper5;}
      default : return -4711;
      }
   }
   
   public static int onlyElse() {
      if (2 == 3) {
         return 2;
      }
      else {
         return -4711;
      }
   }
   
   public static int onlyThen() {
      if (2 == 2) {
         return 2;
      }
      else {
         return -4711;
      }
   }
   
   public static int ifNoBlock(int x, int y) {
      if (x < y) return x;
      else return y;
   }
   
   public static int simpleBlock() {
      int x = 2;
      {
         x++;
         x--;
      }
      {
         x++;
      }
      return x;
   }
   
   public static int nestedIf(int x, int y, int z) {
      if (x < y) {
         if (y < z) {
            return x;
         }
      }
      return -1;
   }
   
   public static int min(int x, int y) {
      int result;
      if (x < y) {
         return x;
      }
      else {
         result = y;
      }
      return result;
   }
}
