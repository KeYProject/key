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

import org.key_project.util.java.NumberUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Table model to display information on the caching database.
 * Has four columns: name, java source, info and size on disk.
 *
 * @author Arne Keller
 */
public class CachingDatabaseTable extends AbstractTableModel {

    private static final Logger LOGGER = LoggerFactory.getLogger(CachingDatabaseTable.class);

    /**
     * The caching database.
     */
    private final CachingDatabase database;
    /**
     * Cached proofs to show in this table.
     * The order of this list determines the order of the table.
     */
    private List<Path> cachedProofs;
    /**
     * Cached branches to display in the table. These will only be shown as a total for each proof.
     */
    private Map<Path, List<CachedProofBranch>> cache;
    /**
     * For each proof in {@link #cachedProofs}: the size on disk, formatted as human-readable
     * number.
     */
    private List<String> sizeOnDisk;

    /**
     * Construct a new table model for the specified database.
     *
     * @param database caching database to show
     */
    CachingDatabaseTable(CachingDatabase database) {
        this.database = database;
        refresh();
    }

    /**
     * Refresh this model's data based on the current state of the database.
     */
    public void refresh() {
        cachedProofs = new ArrayList<>(database.getAllCachedProofs());
        cache = database.getAllCachedProofBranches();
        // for each proof, compute the size on disk
        sizeOnDisk = new ArrayList<>();
        for (var cachedProof : cachedProofs) {
            try {
                sizeOnDisk.add(NumberUtil.formatAsHumanReadableSize(
                    database.sizeOfCachedProof(cache.get(cachedProof).get(0))));
            } catch (IOException e) {
                LOGGER.warn("failed to determine proof size ", e);
                sizeOnDisk.add("???");
            }
        }
    }

    @Override
    public int getRowCount() {
        return cachedProofs.size();
    }

    @Override
    public int getColumnCount() {
        return 4;
    }

    @Override
    public String getColumnName(int columnIndex) {
        return switch (columnIndex) {
        case 0 -> "Proof";
        case 1 -> "Java source";
        case 2 -> "Info";
        case 3 -> "Size on disk";
        default -> "??";
        };
    }

    @Override
    public Class<?> getColumnClass(int columnIndex) {
        return switch (columnIndex) {
        case 0, 1, 2, 3 -> String.class;
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
        case 3 -> sizeOnDisk.get(rowIndex);
        default -> null;
        };
    }

    @Override
    public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
        throw new IllegalStateException();
    }

    /**
     * Delete the proof at the specified row from the database,
     * and refresh the model afterward.
     *
     * @param rowIndex row index of proof to remove
     */
    public void deleteProof(int rowIndex) throws IOException {
        database.removeProof(cachedProofs.get(rowIndex));
        refresh();
    }
}
