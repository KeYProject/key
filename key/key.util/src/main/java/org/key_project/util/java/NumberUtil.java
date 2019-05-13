package org.key_project.util.java;

/**
 * Provides utility methods to work with numbers.
 * @author Martin Hentschel
 */
public class NumberUtil {
   /**
    * The maximal number of digits of an integer value.
    */
   public static final byte MAX_INT_DIGITS = numberOfDigits(Integer.MAX_VALUE);
   
   /**
    * The maximal number of digits of a long value.
    */
   public static final byte MAX_LONG_DIGITS = numberOfDigits(Long.MAX_VALUE);
   
   /**
    * Forbid instances.
    */
   private NumberUtil() {
   }
   
   /**
    * Converts the number into a {@link String} including the algebraic sign
    * and the maximal number of leading zeros.
    * @param number The number to convert.
    * @return The number as full {@link String}.
    */
   public static String toFullString(int number) {
      int numOfDigits = numberOfDigits(number);
      StringBuilder sb = new StringBuilder();
      sb.append(getAlgebraicSign(number));
      for (int i = 0; i < MAX_INT_DIGITS - numOfDigits; i++) {
         sb.append("0");
      }
      String numberString = Integer.toString(number);
      if (numberString.startsWith("-")) {
         sb.append(numberString.substring(1));
      }
      else {
         sb.append(number);
      }
      return sb.toString();
   }
   
   /**
    * Converts the number into a {@link String} including the algebraic sign
    * and the maximal number of leading zeros.
    * @param number The number to convert.
    * @return The number as full {@link String}.
    */
   public static String toFullString(long number) {
      int numOfDigits = numberOfDigits(number);
      StringBuilder sb = new StringBuilder();
      sb.append(getAlgebraicSign(number));
      for (int i = 0; i < MAX_LONG_DIGITS - numOfDigits; i++) {
         sb.append("0");
      }
      String numberString = Long.toString(number);
      if (numberString.startsWith("-")) {
         sb.append(numberString.substring(1));
      }
      else {
         sb.append(number);
      }
      return sb.toString();
   }
   
   /**
    * Returns the algebraic sign.
    * @param number The number. 
    * @return {@code '+'} for zero and positive numbers, {@code '-'} for negative numbers.
    */
   public static char getAlgebraicSign(long number) {
      if (number < 0) {
         return '-';
      }
      else {
         return '+';
      }
   }
   
   /**
    * Returns the algebraic sign.
    * @param number The number. 
    * @return {@code '+'} for zero and positive numbers, {@code '-'} for negative numbers.
    */
   public static char getAlgebraicSign(int number) {
      if (number < 0) {
         return '-';
      }
      else {
         return '+';
      }
   }
   
   /**
    * Returns the number of digits of the given number ignoring the algebraic sign (+/-).
    * @param number The number to compute the number of its digits.
    * @return The number.
    */
   public static byte numberOfDigits(int number) {
      if (number == 0) {
         return 1;
      }
      else {
         byte digits = 0;
         while (number != 0) {
            digits++;
            number = number / 10;
         }
         return digits;
      }
   }
   
   /**
    * Returns the number of digits of the given number ignoring the algebraic sign (+/-).
    * @param number The number to compute the number of its digits.
    * @return The number.
    */
   public static byte numberOfDigits(long number) {
      if (number == 0) {
         return 1;
      }
      else {
         byte digits = 0;
         while (number != 0) {
            digits++;
            number = number / 10;
         }
         return digits;
      }
   }

   /**
    * Parses the given full text.
    * @param text The full text.
    * @return The int value.
    */
   public static int parseFullInt(String text) {
      if (text != null) {
         if (text.startsWith("+")) {
            text = text.substring(1);
         }
         return Integer.valueOf(text);
      }
      else {
         throw new NumberFormatException("Text not defined.");
      }
   }

   /**
    * Parses the given full text.
    * @param text The full text.
    * @return The long value.
    */
   public static long parseFullLong(String text) {
      if (text != null) {
         if (text.startsWith("+")) {
            text = text.substring(1);
         }
         return Long.valueOf(text);
      }
      else {
         throw new NumberFormatException("Text not defined.");
      }
   }
}
