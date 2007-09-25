class C {
    
    static boolean result1, result2, result3, result4;

    static void m() {
	result1 = C1.b1; result2 = C2.b2;
	result3 = C1.d1; result4 = C2.d2;
    }        
}

class C1 {
    static boolean b1 = C2.d2;
    static boolean d1 = true;
}

class C2 {
    static boolean d2 = true;
    static boolean b2 = C1.d1;
}
