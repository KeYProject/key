/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

public class ClassA {
	private int x = 5;
	
	/*@
    @ public normal_behavior
    @ requires true;
    @ ensures x == 5;
    @ assignable \nothing;
    @*/		
	public ClassA() {
	}
	
	/*@
    @ public normal_behavior
    @ requires true;
    @ ensures this.x == x;
    @ assignable \nothing;
    @*/		
	public ClassA(int x) {
		this.x = x;
	}

    /*@
    @ public normal_behavior
    @ requires true;
    @ ensures \result == x;
    @ assignable \nothing;
    @*/	
	public int getX() {
		return x;
	}

    /*@
    @ public normal_behavior
    @ requires true;
    @ ensures this.x == x;
    @ assignable \nothing;
    @*/		
	public void setX(int x) {
		this.x = x;
	}
}