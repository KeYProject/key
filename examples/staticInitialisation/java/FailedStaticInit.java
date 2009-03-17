// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class FailedStaticInit {

    public static int ATTR;
 
    static {
	A.SAVE = new FailedStaticInit();
	int a = 0 / (3-3);
    }

    public int objectVar = 0;

    public FailedStaticInit() {
    }

    public void objectMethod() {
	this.objectVar = 3;
        FailedStaticInit.ATTR = 0;
    }

}
