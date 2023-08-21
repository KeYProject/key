/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.*;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import javax.swing.*;
import javax.swing.event.TableModelEvent;
import javax.swing.event.TableModelListener;
import javax.swing.table.TableModel;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;

/**
 * Table showing the results of searching for proof references.
 *
 * @author Arne Keller
 */
class ReferenceSearchTable extends JTable implements TableModel {
    /**
     * The mediator.
     */
    private final KeYMediator mediator;
    /**
     * List of open and closed goals in the selected proof.
     */
    private final List<Goal> goals;

    /**
     * Construct a new table.
     *
     * @param proof proof to analyze
     * @param mediator the mediator
     */
    public ReferenceSearchTable(Proof proof, KeYMediator mediator) {
        this.setModel(this);
        this.goals = proof.allGoals().stream()
                .filter(g -> !g.node().isClosed() || g.node().lookup(ClosedBy.class) != null)
                .collect(Collectors.toList());
        Collections.reverse(this.goals);
        this.mediator = mediator;
        getColumnModel().getColumn(1).setMinWidth(200);
    }

    @Override
    public Dimension getPreferredSize() {
        Dimension d = super.getPreferredSize();
        return new Dimension(d.width + 100, d.height);
    }

    @Override
    public void addTableModelListener(TableModelListener l) {

    }

    @Override
    public void removeTableModelListener(TableModelListener l) {

    }

    @Override
    public int getRowCount() {
        return goals.size();
    }

    @Override
    public int getColumnCount() {
        return 2;
    }

    @Override
    public String getColumnName(int column) {
        switch (column) {
        case 0:
            return "Goal";
        case 1:
            return "Reference";
        default:
            return "??";
        }
    }

    @Override
    public Class<?> getColumnClass(int column) {
        return String.class;
    }

    @Override
    public Object getValueAt(int row, int column) {
        if (column == 0) {
            return String.valueOf(goals.get(row).node().serialNr());
        } else {
            Goal g = goals.get(row);
            ClosedBy c = g.node().lookup(ClosedBy.class);
            if (c == null) {
                return "no reference found";
            } else {
                int i = mediator.getCurrentlyOpenedProofs().indexOf(c.getProof()) + 1;
                return String.format("reference available (proof %d, node %d)", i,
                    c.getNode().serialNr());
            }
        }
    }

    @Override
    public boolean isCellEditable(int row, int column) {
        return false;
    }

    @Override
    public void tableChanged(TableModelEvent e) {
        if (e.getType() == TableModelEvent.UPDATE) {
            this.repaint();

        }
        super.tableChanged(e);
    }

}
