/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.io.File;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import javax.swing.*;
import javax.swing.table.AbstractTableModel;

public class CachingDatabaseTable extends AbstractTableModel {

    private final CachingDatabase database;
    private List<Path> cachedProofs;
    private Map<Path, List<CachedProofBranch>> cache;

    CachingDatabaseTable(CachingDatabase database) {
        this.database = database;
        refresh();
    }

    public void refresh() {
        cachedProofs = new ArrayList<>(database.getAllCachedProofs());
        cache = database.getAllCachedProofBranches();
    }

    @Override
    public int getRowCount() {
        return cachedProofs.size();
    }

    @Override
    public int getColumnCount() {
        return 3;
    }

    @Override
    public String getColumnName(int columnIndex) {
        switch (columnIndex) {
        case 0:
            return "Proof";
        case 1:
            return "Java source";
        case 2:
            return "Info";
        default:
            return "??";
        }
    }

    @Override
    public Class<?> getColumnClass(int columnIndex) {
        return switch (columnIndex) {
        case 0 -> File.class;
        case 1, 2 -> String.class;
        default -> null;
        };
    }

    @Override
    public boolean isCellEditable(int rowIndex, int columnIndex) {
        return false;
    }

    @Override
    public Object getValueAt(int rowIndex, int columnIndex) {
        switch (columnIndex) {
        case 0:
            return cache.get(cachedProofs.get(rowIndex)).get(0).proofName;
        case 1:
            return "?";
        case 2:
            var proof = cachedProofs.get(rowIndex);
            var data = cache.get(proof);
            return String.format("Branches: %d", data.size());
        default:
            return null;
        }
    }

    @Override
    public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
        throw new IllegalStateException();
    }
}
