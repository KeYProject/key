package org.key_project.sed.core.model;

/**
 * Classes that implements this interface provides the path of a file
 * that is treated, edited or what else.
 * @author Martin Hentschel
 */
public interface ISourcePathProvider {
   /**
    * Returns the source path.
    * @return The source path.
    */
   public String getSourcePath();
}
