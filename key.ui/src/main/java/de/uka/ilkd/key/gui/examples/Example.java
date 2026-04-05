package de.uka.ilkd.key.gui.examples;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Enumeration;
import java.util.List;

/**
 * This class wraps a {@link File} and has a special {@link #toString()} method only using the
 * short file name w/o path.
 * <p>
 * Used for displaying files in the examples list w/o prefix
 * @param name
 * @param treePath
 * @param directory
 * @param description
 * @param keyFile
 * @param keyProof
 * @param additionalFiles
 */
@NullMarked
public record Example(String name,
                      List<String> treePath,
                      Path directory,
                      String description,
                      Path keyFile,
                      @Nullable Path keyProof,
                      List<Path> additionalFiles) {
    public File getDirectory() {
        return directory.toFile();
    }

    public String getDescription() {
        return description;
    }

    @Override
    public String toString() {
        return name();
    }

    public void addToTreeModel(DefaultTreeModel model) {
        DefaultMutableTreeNode node =
                findChild((DefaultMutableTreeNode) model.getRoot(), treePath(), 0);
        node.add(new DefaultMutableTreeNode(this));
    }

    private DefaultMutableTreeNode findChild(DefaultMutableTreeNode root,
                                             List<String> path,
                                             int from) {
        if (from == path.size()) {
            return root;
        }
        Enumeration<?> en = root.children();
        while (en.hasMoreElements()) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode) en.nextElement();
            if (node.getUserObject().equals(path.get(from))) {
                return findChild(node, path, from + 1);
            }
        }
        // not found ==> add new
        DefaultMutableTreeNode node = new DefaultMutableTreeNode(path.get(from));
        root.add(node);
        return findChild(node, path, from + 1);
    }

    public boolean hasProof() {
        return keyProof != null && Files.exists(keyProof);

    }

}
