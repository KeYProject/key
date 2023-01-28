package enumtest.jls;

/*
 * Taken from JLS, 3rd edition (draft), pg. 256f,
 * with modification to actually run ;-)
 */

import java.util.*;

public enum Operation {
	PLUS {
		double eval(double x, double y) {
			return x + y;
		}
	},
	MINUS {
		double eval(double x, double y) {
			return x - y;
		}
	},
	TIMES {
		double eval(double x, double y) {
			return x * y;
		}
	},
	DIVIDED_BY {
		double eval(double x, double y) {
			return x / y;
		}
	};
	
	// this is needed here to actually run...
	abstract double eval(double x, double y);

	// Perform the arithmetic operation represented by this constant
	// abstract double eval(double x, double y);

	public static void main(String args[]) {
		double x = Double.parseDouble(args[0]);
		double y = Double.parseDouble(args[1]);
		for (Operation op : Operation.values())
			System.out.println(x + " " + op + " " + y + " = " + op.eval(x, y));
		// an additional test:
		TIMES.eval(1.0, 2.0); // check for references to type!
	}
}
