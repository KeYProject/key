/**
 * This class provides general utility methods dealing with integer numbers.
 */
public class IntegerUtil {
   /**
    * Returns the middle value of {@code x}, {@code y} and {@code z}.
    * @param x The first integer number.
    * @param y The second integer number.
    * @param z The third integer number.
    * @return The middle value of {@code x}, {@code y} and {@code z}.
    */
	public static int middle(int x, int y, int z) {
		if (y < z) {
			if (x < y) {
				return y;
			}
			else {
			   if (x < z) {
				   return y;
			   }
			}
		}
		else {
			if (x > y) {
				return y;
			}
			else {
			   if (x > z) {
				   return x;
				}
			}
		}
		return z;
	}
}