/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.database;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import javax.swing.table.AbstractTableModel;

import de.uka.ilkd.key.gui.plugins.caching.CachedProofBranch;

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
        return switch (columnIndex) {
        case 0 -> "Proof";
        case 1 -> "Java source";
        case 2 -> "Info";
        default -> "??";
        };
    }

    @Override
    public Class<?> getColumnClass(int columnIndex) {
        return switch (columnIndex) {
        case 0, 1, 2 -> String.class;
        default -> null;
        };
    }

    @Override
    public boolean isCellEditable(int rowIndex, int columnIndex) {
        return false;
    }

    @Override
    public Object getValueAt(int rowIndex, int columnIndex) {
        var proofPath = cachedProofs.get(rowIndex);
        return switch (columnIndex) {
        case 0 -> cache.get(proofPath).get(0).proofName;
        case 1 -> Arrays.toString(cache.get(proofPath).get(0).getJavaClasses().toArray());
        case 2 -> {
            var data = cache.get(proofPath);
            yield String.format("Branches: %d", data.size());
        }
        default -> null;
        };
    }

    @Override
    public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
        throw new IllegalStateException();
    }

    /**
     * Delete the proof at the specified row from the database.
     *
     * @param rowIndex row index of proof to remove
     */
    public void deleteProof(int rowIndex) throws IOException {
        database.removeProof(cachedProofs.get(rowIndex));
        refresh();
    }
}
