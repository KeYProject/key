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

public class MCDemo {
	int attr;
	
	/*@
	  @ public normal_behavior
	  @ assignable \nothing;
	  @ ensures \result == x+1;
	  @*/
	public int inc(int x) {
		return ++x;
	}
    
	/*@
	  @ public normal_behavior
	  @ ensures \result == u+1 && attr == 100;
	  @*/
	public int init(int u) {
		attr = 100;
		return inc(u);
	}
}