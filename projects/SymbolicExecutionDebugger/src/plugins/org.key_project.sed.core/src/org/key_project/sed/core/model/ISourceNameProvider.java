package org.key_project.sed.core.model;

/**
 * Classes that implements this interface provides the name of a file
 * that is treated, edited or what else.
 * @author Martin Hentschel
 */
public interface ISourceNameProvider {
   /**
    * Returns the source name.
    * @return The source name.
    */
   public String getSourceName();
}
