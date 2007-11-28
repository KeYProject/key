// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;

/** This class is responsible for the translation of type boundary <tt>String</tt>s into their 
 * actual values.
 *  
 * @author akuwertz
 * @version 1.0,  03/31/2006 
 */

public class TypeBoundTranslation {
    
    /** The array of <tt>String</tt> representations of the type boundary values */
    private static final String[][] typeBounds = new String[][]
        {
            // Int bounds
            {
                "-2147483648",  //MIN
                "2147483647",   //MAX
                "2147483648",   //HALFRANGE
                "4294967296"    //RANGE 
            },     

            // Char bounds
            {
                "0",      //MIN  
                "65535",  //MAX
                null,     // NullPointerException for char_HALFRANGE
                "65535"   //RANGE
            },    
                
            // Long bounds
            {
                "-9223372036854775808",  //MIN
                "9223372036854775807",   //MAX
                "9223372036854775808",   //HALFRANGE
                "18446744073709551616"   //RANGE
            },    
        
            // Byte bounds
            {
                "-128",  //MIN
                "127",   //MAX
                "128",   //HALFRANGE
                "256"    //RANGE
            },    
        
            // Short bounds
            {
                "-32768",  //MIN
                "32767",   //MAX
                "32768",   //HALFRANGE
                "65536"    //RANGE
            }    
        };    
    
    /** String constants for wrong boundary specifiers */ 
    private static final String noTypeBoundString = 
        "The given string constant does not represent a valid type boudary!";

    
    /** Make the constructor private */
    private TypeBoundTranslation() {
        super();
    }
    
    
    
    /* Public method implementation */
    
    /** Returns a <tt>String</tt> representation of the value of a type boundary specified by 
     * the argument <tt>String</tt> <tt>typeBound</tt>
     * 
     * @param typeBound the type boundary to be translated into a value
     * @throws IllegalArgumentException if <tt>typeBound</tt> represent no valid type boundary
     */
    public static String getTypeBoundValue( String typeBound ) {

        int indexOne, indexTwo;
        
        // Parse type constraint
        String[] parts = typeBound.split( "_" );
        String partOne = parts[0];
        String partTwo = parts[1];                      
        
        // Compare data type
        if      ( partOne.equals( "int" ) )   indexOne = 0;
        else if ( partOne.equals( "char" ) )  indexOne = 1;
        else if ( partOne.equals( "long" ) )  indexOne = 2;
        else if ( partOne.equals( "byte" ) )  indexOne = 3;
        else if ( partOne.equals( "short" ) ) indexOne = 4;       
        else throw new IllegalArgumentException( noTypeBoundString );
        
        // compare constraint
        if      ( partTwo.equals( "MIN" ) )       indexTwo = 0;
        else if ( partTwo.equals( "MAX" ) )       indexTwo = 1;
        else if ( partTwo.equals( "HALFRANGE" ) ) indexTwo = 2;
        else if ( partTwo.equals( "RANGE" ) )     indexTwo = 3;
        else throw new IllegalArgumentException( noTypeBoundString );
            
        return typeBounds[ indexOne ][ indexTwo ];
    }
}
