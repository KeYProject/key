/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;
import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class in an implementation of the {@link Transferable} interface and allows to transfer a
 * {@link PosInSequent} object. It supports to data flavors:
 * <ul>
 * <li>{@link PosInSequentTransferable#POS_IN_SEQUENT_TRANSFER} flavor which is of mime type
 * {@link DataFlavor#javaJVMLocalObjectMimeType}</li>
 * <li>{@link DataFlavor#stringFlavor} which returns the term described by the
 * {@link de.uka.ilkd.key.pp.PosInSequent} as a parsable string</li>
 * </ul>
 */
@NullMarked
public class PosInSequentTransferable implements Transferable {
    private static final Logger LOGGER = LoggerFactory.getLogger(PosInSequentTransferable.class);

    /**
     * The transfer flavor for the platform-local sequent objects. See
     * {@link #createTransferFlavor()} for the fallback when the platform-local mime type is
     * unavailable.
     */
    public static DataFlavor POS_IN_SEQUENT_TRANSFER = createTransferFlavor();

    /**
     * Creates the transfer flavor for the platform-local sequent objects.
     *
     * <p>
     * The platform-local mime type is a hard-coded JDK constant that is normally always
     * available; if it is ever not, the string flavor is returned so that the flavor field is
     * never {@code null}.
     *
     * @return the created transfer flavor
     */
    private static DataFlavor createTransferFlavor() {
        try {
            return new DataFlavor(DataFlavor.javaJVMLocalObjectMimeType);
        } catch (ClassNotFoundException e) {
            LOGGER.info("POS_IN_SEQUENT_TRANSFER not supported, using string flavor behaviour", e);
            return DataFlavor.stringFlavor;
        }
    }

    /** the highlighted position in the sequentview to be transferred */
    private final PosInSequent pis;

    /** the highlighted term as parseable string */
    private String stringSelection;

    /**
     * Creates an instance of this transferable.
     *
     * <p>
     * The string selection is only computed for term positions; the EISOP initialization check
     * cannot see that the field is only ever read for term transfers, so the conditionally
     * initialized field is suppressed with a scoped key.
     *
     * @param pis the PosInSequent to be transfered (string flavor only supported if pis denotes a
     *        term or formula, not the complete sequent)
     */
    @SuppressWarnings("nullness:initialization.fields.uninitialized")
    public PosInSequentTransferable(PosInSequent pis, Services serv) {
        this.pis = pis;
        if (!pis.isSequent()) {
            PosInOccurrence pio = pis.getPosInOccurrence();
            if (pio == null) {
                // a non-sequent position always carries a term position
                throw new NullPointerException("No position in sequent available.");
            }
            this.stringSelection =
                ProofSaver.printTerm((JTerm) pio.subTerm(), serv);
        }
    }

    /**
     * returns the supported flavors of this transferable. These are currently
     * {@link DataFlavor#stringFlavor} and {@link PosInSequentTransferable#POS_IN_SEQUENT_TRANSFER}
     *
     * @see java.awt.datatransfer.Transferable#getTransferDataFlavors()
     */
    public DataFlavor[] getTransferDataFlavors() {
        return new DataFlavor[] { POS_IN_SEQUENT_TRANSFER, DataFlavor.stringFlavor };
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * java.awt.datatransfer.Transferable#isDataFlavorSupported(java.awt.datatransfer.DataFlavor)
     */
    public boolean isDataFlavorSupported(@Nullable DataFlavor flavor) {
        return flavor != null && (flavor.equals(POS_IN_SEQUENT_TRANSFER)
                || flavor.equals(DataFlavor.stringFlavor));
    }

    /**
     * if the flavor is equal to the {@link PosInSequentTransferable#POS_IN_SEQUENT_TRANSFER} the
     * return data is of kind {@link PosInSequent}. If the flavor equals
     * {@link DataFlavor#stringFlavor} the highlighted term is returned as parsable string.
     *
     * <p>
     * An unsupported request (including a {@code null} flavor) is reported through the
     * exception; the exception constructor declares a non-null flavor while a {@code null}
     * request is per definition unsupported, suppressed with a scoped key.
     *
     * @throws UnsupportedFlavorException if the flavor is not supported
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    public Object getTransferData(@Nullable DataFlavor flavor)
            throws UnsupportedFlavorException, IOException {
        if (flavor != null) {
            if (flavor.equals(POS_IN_SEQUENT_TRANSFER)) {
                return pis;
            } else if (flavor.equals(DataFlavor.stringFlavor)) {
                return stringSelection;
            }
        }
        throw new UnsupportedFlavorException(flavor);
    }

}
