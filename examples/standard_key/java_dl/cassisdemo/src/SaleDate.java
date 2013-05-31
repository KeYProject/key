// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package src;

public class SaleDate {
    int year=0;;
    int month=0;
    int day=0;

    public SaleDate(){
        year=2004;
        month = 1;
        day = 1;
    }

    public SaleDate(int year, int month, int day){
	this.year = year;
        this.month = month;
        this.day = day;
    }
}
