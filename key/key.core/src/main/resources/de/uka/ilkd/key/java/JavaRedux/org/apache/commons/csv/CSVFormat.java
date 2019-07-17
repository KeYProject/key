package org.apache.commons.csv;

/**
 * @generated
 */
public final class CSVFormat extends java.lang.Object implements java.io.Serializable {
   /**
    * @generated
    */
   public static final org.apache.commons.csv.CSVFormat RFC4180;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.apache.commons.csv.CSVParser parse(java.io.Reader param0) throws java.io.IOException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.apache.commons.csv.CSVPrinter print(java.lang.Appendable param0) throws java.io.IOException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.apache.commons.csv.CSVFormat withDelimiter(char param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.apache.commons.csv.CSVFormat withFirstRecordAsHeader();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public org.apache.commons.csv.CSVFormat withHeader(java.lang.String[] param0);
}