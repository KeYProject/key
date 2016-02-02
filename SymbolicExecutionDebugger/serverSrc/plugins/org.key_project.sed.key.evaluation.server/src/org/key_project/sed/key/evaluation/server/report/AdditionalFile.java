package org.key_project.sed.key.evaluation.server.report;

/**
 * An additional file to create.
 * @author Martin Hentschel
 */
public class AdditionalFile {
   /**
    * The suffix of the file name.
    */
   private final String nameSuffix;
   
   /**
    * The content.
    */
   private final byte[] content;

   /**
    * Constructor.
    * @param nameSuffix The suffix of the file name.
    * @param content The content.
    */
   public AdditionalFile(String nameSuffix, byte[] content) {
      this.nameSuffix = nameSuffix;
      this.content = content;
   }

   /**
    * Returns the suffix of the file name.
    * @return The suffix of the file name.
    */
   public String getNameSuffix() {
      return nameSuffix;
   }

   /**
    * Returns the content.
    * @return The content.
    */
   public byte[] getContent() {
      return content;
   }
}