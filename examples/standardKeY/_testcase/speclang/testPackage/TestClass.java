// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package testPackage;

public class TestClass {

    byte b;
    short s;
    int i;
    long l;

    TestClass[] array;

    public static TestClass instance = new TestClass();

    public int getOne() {
        return 1;
    }

    public int m(int a) {
        return 2;
    }

    public int m(long a) {
        return 3;
    }

    public static int staticMethod() {
        return 4;
    }

}

