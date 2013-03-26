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


/*
 * Created on Apr 17, 2005
 */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;
import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * This class in an implementation of the {@link Transferable} interface and
 * allows to transfer a {@link PosInSequent} object.
 * It supports to data flavors:
 * <ul>
 * <li> {@link PosInSequentTransferable#POS_IN_SEQUENT_TRANSFER} flavor which is 
 *   of mime type {@link DataFlavor#javaJVMLocalObjectMimeType}</li>
 * <li> {@link DataFlavor#stringFlavor} which returns the term described 
 * by the {@link de.uka.ilkd.key.pp.PosInSequent} as a parsable string </li>
 * </ul>
 */
public class PosInSequentTransferable implements Transferable {

    public static DataFlavor POS_IN_SEQUENT_TRANSFER;
    static {
        try {
            POS_IN_SEQUENT_TRANSFER = 
                new DataFlavor(DataFlavor.javaJVMLocalObjectMimeType);
        } catch (ClassNotFoundException e) {
            // POS_IN_SEQUENT_TRANSFER not supported use 
            // string flavor behaviour
            e.printStackTrace();
        }
    }
    
    /** the highlighted position in the sequentview to be transferred */ 
    private PosInSequent pis;
    
    /** the highlighted term as parseable string */
    private String stringSelection;
    
    
    /** 
     * creates an instance of this transferable      
     * @param pis the PosInSequent to be transfered
     * (string flavor only supported if pis denotes a term or formula, not the 
     *  complete sequent)     
     */
    public PosInSequentTransferable(PosInSequent pis, Services serv) {
        this.pis = pis;
        if (!pis.isSequent()) {
            this.stringSelection = ProofSaver.
                printTerm(pis.getPosInOccurrence().subTerm(), serv).toString();
        }
    }
    
    /** 
     * returns the supported flavors of this transferable. These are
     * currently {@link DataFlavor#stringFlavor} and 
     * {@link PosInSequentTransferable#POS_IN_SEQUENT_TRANSFER}
     * 
     * @see java.awt.datatransfer.Transferable#getTransferDataFlavors()
     */
    public DataFlavor[] getTransferDataFlavors() {              
        return new DataFlavor[]{POS_IN_SEQUENT_TRANSFER, DataFlavor.stringFlavor};
    }

    /* (non-Javadoc)
     * @see java.awt.datatransfer.Transferable#isDataFlavorSupported(java.awt.datatransfer.DataFlavor)
     */
    public boolean isDataFlavorSupported(DataFlavor flavor) {
        return flavor != null && (flavor.equals(POS_IN_SEQUENT_TRANSFER) 
                || flavor.equals(DataFlavor.stringFlavor));
    }

    /**
     * if the flavor is equal to the 
     * {@link PosInSequentTransferable#POS_IN_SEQUENT_TRANSFER} the return data
     * is of kind {@link PosInSequent}. If the flavor equals 
     * {@link DataFlavor#stringFlavor} the highlighted term is returned as 
     * parsable string. 
     * @throws UnsupportedFlavorException if the flavor is not supported
     */      
    public Object getTransferData(DataFlavor flavor) 
    throws UnsupportedFlavorException, IOException {       
        if (flavor != null) {
            if (flavor.equals(POS_IN_SEQUENT_TRANSFER)) {
                return pis;
            } else if (flavor.equals(DataFlavor.stringFlavor)){
                return stringSelection;
            }
        } 
        throw new UnsupportedFlavorException(flavor);
    }

}
