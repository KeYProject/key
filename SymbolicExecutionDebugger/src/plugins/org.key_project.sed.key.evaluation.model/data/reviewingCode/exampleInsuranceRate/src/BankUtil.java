/**
 * This class provides utility methods for a banking application.
 */
public class BankUtil {
   /**
    * Computes the insurance rate based on the given age.
    * @param age The requested age.
    * @return The insurance rate according to the age:
    * <ul>
    *    <li>{@code 200} if {@code age < 18}</li>
    *    <li>{@code 250} if {@code age >= 18} and {@code age < 19}</li>
    *    <li>{@code 300} if {@code age >= 19} and {@code age < 21}</li>
    *    <li>{@code 450} if {@code age >= 21} and {@code age < 35}</li>
    *    <li>{@code 575} if {@code age >= 35}</li>
    * <ul>
    */
   public static long computeInsuranceRate(int age) {
      int[] ageLimits = {18, 19, 21, 35, 65};
      long[] insuranceRates = {200, 250, 300, 450, 575};
      int ageLevel = 0;
      long insuranceRate = 570;
      while (ageLevel < ageLimits.length - 1) {
         if (age < ageLimits[ageLevel]) {
            return insuranceRates[ageLevel];
         }
         ageLevel++;
      }
      return insuranceRate;
   }
}