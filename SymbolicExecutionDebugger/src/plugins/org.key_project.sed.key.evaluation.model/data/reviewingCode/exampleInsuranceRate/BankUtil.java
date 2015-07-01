public class BankUtil {
   /**
    * Computes the insurance rate based on the given age.
    * @param age The requested age.
    * @return The insurance rate according to the age:
    * <ul>
    *    <li>{@code 200} if age < {@code 18}</li>
    *    <li>{@code 250} if age >= {@code 18} and age < {@code 19}</li>
    *    <li>{@code 300} if age >= {@code 19} and age < {@code 21}</li>
    *    <li>{@code 450} if age >= {@code 21} and age < {@code 35}</li>
    *    <li>{@code 575} if age >= {@code 35}</li>
    * <ul>
    */
   public static long computeInsuranceRate(int age) {
      int[] ageLimits = {18, 19, 21, 35, 65};
      long[] insuranceRates = {200, 250, 300, 450};
      int ageLevel = 0;
      long insuranceRate = 575;
      while (insuranceRate == 575 && ageLevel < ageLimits.length - 1) {
         if (age < ageLimits[ageLevel]) {
            return insuranceRates[ageLevel];
         }
         ageLevel++;
      }
      return insuranceRate;
   }
}