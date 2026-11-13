/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;
import java.awt.event.InputEvent;
import java.io.IOException;
import java.util.EnumMap;
import java.util.Map;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.prover.sequent.Sequent;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class in an implementation of the {@link Transferable} interface and allows to transfer a
 * {@link PosInSequent} object. It supports two data flavors:
 * <ul>
 * <li>{@link PosInSequentTransferable#POS_IN_SEQUENT_TRANSFER} flavor which is of mime type
 * {@link DataFlavor#javaJVMLocalObjectMimeType}</li>
 * <li>{@link DataFlavor#stringFlavor} which returns the term described by the
 * {@link de.uka.ilkd.key.pp.PosInSequent} as a string</li>
 * </ul>
 * <p>
 * The string is printed lazily when the flavor is first read, in one of the
 * {@link PrintMode print modes}. While dragging, the mode is chosen with the keyboard modifiers
 * (Shift: safe ASCII, Ctrl: term structure) and can be updated by drag source listeners via
 * {@link #setPrintMode(PrintMode)}.
 */
public class PosInSequentTransferable implements Transferable {
    private static final Logger LOGGER = LoggerFactory.getLogger(PosInSequentTransferable.class);

    public static DataFlavor POS_IN_SEQUENT_TRANSFER;
    static {
        try {
            POS_IN_SEQUENT_TRANSFER = new DataFlavor(DataFlavor.javaJVMLocalObjectMimeType);
        } catch (ClassNotFoundException e) {
            LOGGER.info("POS_IN_SEQUENT_TRANSFER not supported, using string flavor behaviour", e);
        }
    }

    /**
     * How the transferred content is printed for the string flavor.
     */
    public enum PrintMode {
        /**
         * Pretty-printed following the currently activated view settings (notation info and term
         * label visibility of the sequent view).
         */
        PRETTY,
        /**
         * Pretty-printed with safe settings: no unicode symbols, package prefixes shown and all
         * term labels shown (except the ones KeY always hides).
         */
        SAFE,
        /** Non-pretty-printed term structure. */
        STRUCTURE;

        /**
         * Selects the print mode for the given drag gesture modifiers: Shift selects
         * {@link #SAFE}, Ctrl selects {@link #STRUCTURE}, without a modifier {@link #PRETTY}.
         *
         * @param modifiersEx the extended modifiers of the drag gesture
         * @return the print mode for the given modifiers
         */
        public static PrintMode of(int modifiersEx) {
            if ((modifiersEx & InputEvent.SHIFT_DOWN_MASK) != 0) {
                return SAFE;
            }
            if ((modifiersEx & InputEvent.CTRL_DOWN_MASK) != 0) {
                return STRUCTURE;
            }
            return PRETTY;
        }
    }

    /** the highlighted position in the sequentview to be transferred */
    private final PosInSequent pis;

    /** the services (term printing) */
    private final Services services;

    /** the displayed sequent; provides the string flavor when {@code pis} denotes the sequent */
    private final @Nullable Sequent wholeSequent;

    /** the notation info of the view, used for {@link PrintMode#PRETTY} printing */
    private final NotationInfo notationInfo;

    /** the visible term labels of the view, used for {@link PrintMode#PRETTY} printing */
    private final @Nullable VisibleTermLabels visibleTermLabels;

    /** the print mode currently applied on the string flavor */
    private PrintMode printMode;

    /** the printed string per print mode (values may be {@code null}); printed lazily */
    private final Map<PrintMode, String> printed = new EnumMap<>(PrintMode.class);


    /**
     * creates an instance of this transferable
     *
     * @param pis the PosInSequent to be transfered (string flavor only supported if pis denotes a
     *        term or formula, not the complete sequent)
     */
    public PosInSequentTransferable(PosInSequent pis, Services serv) {
        this(pis, serv, null);
    }

    /**
     * creates an instance of this transferable that prints the term structure (as before the
     * print modes were introduced)
     *
     * @param pis the PosInSequent to be transfered
     * @param serv the services (term printing)
     * @param wholeSequent the displayed sequent; provides the string flavor when {@code pis}
     *        denotes the whole sequent
     */
    public PosInSequentTransferable(PosInSequent pis, Services serv,
            @Nullable Sequent wholeSequent) {
        this(pis, serv, new NotationInfo(), null, wholeSequent, PrintMode.STRUCTURE);
    }

    /**
     * creates an instance of this transferable printing with the given notation info and term
     * label visibility (mode {@link PrintMode#PRETTY})
     *
     * @param pis the PosInSequent to be transfered
     * @param serv the services (term printing)
     * @param notationInfo the notation info of the view (pretty printing with its settings)
     * @param visibleTermLabels the visible term labels of the view (may be {@code null})
     * @param wholeSequent the displayed sequent; provides the string flavor when {@code pis}
     *        denotes the whole sequent
     */
    public PosInSequentTransferable(PosInSequent pis, Services serv, NotationInfo notationInfo,
            @Nullable VisibleTermLabels visibleTermLabels, @Nullable Sequent wholeSequent) {
        this(pis, serv, notationInfo, visibleTermLabels, wholeSequent, PrintMode.PRETTY);
    }

    /**
     * creates an instance of this transferable with an explicit initial print mode
     *
     * @param pis the PosInSequent to be transfered
     * @param serv the services (term printing)
     * @param notationInfo the notation info of the view (pretty printing with its settings)
     * @param visibleTermLabels the visible term labels of the view (may be {@code null})
     * @param wholeSequent the displayed sequent; provides the string flavor when {@code pis}
     *        denotes the whole sequent
     * @param printMode the print mode initially applied on the string flavor
     */
    public PosInSequentTransferable(PosInSequent pis, Services serv, NotationInfo notationInfo,
            @Nullable VisibleTermLabels visibleTermLabels, @Nullable Sequent wholeSequent,
            PrintMode printMode) {
        this.pis = pis;
        this.services = serv;
        this.notationInfo = notationInfo;
        this.visibleTermLabels = visibleTermLabels;
        this.wholeSequent = wholeSequent;
        this.printMode = printMode;
    }

    /**
     * Returns the print mode currently applied on the string flavor.
     *
     * @return the print mode
     */
    public PrintMode getPrintMode() {
        return printMode;
    }

    /**
     * Sets the print mode applied on the string flavor. Drag source listeners use this to follow
     * the keyboard modifiers while the drag is in motion.
     *
     * @param printMode the print mode
     */
    public void setPrintMode(PrintMode printMode) {
        this.printMode = printMode;
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
    public boolean isDataFlavorSupported(DataFlavor flavor) {
        return flavor != null && (flavor.equals(POS_IN_SEQUENT_TRANSFER)
                || flavor.equals(DataFlavor.stringFlavor));
    }

    /**
     * if the flavor is equal to the {@link PosInSequentTransferable#POS_IN_SEQUENT_TRANSFER} the
     * return data is of kind {@link PosInSequent}. If the flavor equals
     * {@link DataFlavor#stringFlavor} the highlighted term is returned as string, printed in the
     * current {@link PrintMode}.
     *
     * @throws UnsupportedFlavorException if the flavor is not supported
     */
    public Object getTransferData(DataFlavor flavor)
            throws UnsupportedFlavorException, IOException {
        if (flavor != null) {
            if (flavor.equals(POS_IN_SEQUENT_TRANSFER)) {
                return pis;
            } else if (flavor.equals(DataFlavor.stringFlavor)) {
                return stringSelection();
            }
        }
        throw new UnsupportedFlavorException(flavor);
    }

    /**
     * Returns the string for the current print mode; printed lazily on first access and cached
     * per print mode.
     */
    private @Nullable String stringSelection() {
        if (!printed.containsKey(printMode)) {
            printed.put(printMode, print());
        }
        return printed.get(printMode);
    }

    /**
     * Prints the transferred content in the current print mode.
     */
    private @Nullable String print() {
        if (!pis.isSequent()) {
            JTerm term = (JTerm) pis.getPosInOccurrence().subTerm();
            return switch (printMode) {
                case STRUCTURE -> ProofSaver.printTerm(term, services);
                case PRETTY, SAFE -> {
                    var printer = printer();
                    printer.layouter().beginC();
                    printer.printTerm(term);
                    printer.layouter().end();
                    yield printer.result();
                }
            };
        } else if (wholeSequent != null) {
            return switch (printMode) {
                case STRUCTURE -> wholeSequent.toString();
                case PRETTY, SAFE -> {
                    var printer = printer();
                    printer.printSequent(wholeSequent);
                    yield printer.result();
                }
            };
        }
        return null;
    }

    /**
     * Creates a printer for the current print mode. For {@link PrintMode#PRETTY} the notation
     * info and label visibility of the view are used; for {@link PrintMode#SAFE} fresh ones with
     * the safe settings.
     */
    private SequentViewLogicPrinter printer() {
        if (printMode == PrintMode.SAFE) {
            var ni = new NotationInfo();
            var printer =
                SequentViewLogicPrinter.purePrinter(ni, services, new TermLabelVisibilityManager());
            // The printer constructor refreshes the notation info from the currently activated
            // view settings (see LogicPrinter(NotationInfo, Services, PosTableLayouter)); reapply
            // the safe settings: pretty syntax, no unicode, package prefixes shown.
            if (services != null) {
                ni.refresh(services, true, false, false);
            }
            return printer;
        }
        return SequentViewLogicPrinter.purePrinter(notationInfo, services, visibleTermLabels);
    }
}
