package org.key_project.jmlediting.core.utilities;

/**
 * A Class for containing offsets of Comments. with offsets for comment begin,
 * comment end, content begin, content end
 *
 * @author David Giessing, Moritz Lichter
 *
 */
public class CommentRange {

   public static enum CommentType {
      SINGLE_LINE, MULTI_LINE;
   }

   /**
    * The Comments begin offset including begin sign.
    */
   private final int beginOffset;
   /**
    * The Comments end offset including end signs (Not the eol sign for
    * SingleLine Comments).
    */
   private final int endOffset;

   /**
    * The begin index of the Comments content.
    */
   private final int contentBeginOffset;
   /**
    * The end index of the Comments content.
    */
   private final int contentEndOffset;

   /**
    * The type of the comment.
    */
   private final CommentType type;

   /**
    * Creates a new CommentRange Object.
    *
    * @param offset
    *           The begin offset of the Comment
    * @param end
    *           The end offset of the Comment
    * @param contentOffset
    *           The begin offset of the Content of the Comment
    * @param contentEndOffset
    *           The end offset of the Content of the Comment
    * @param type
    *           the type of the comment, not allowed to be null
    */
   public CommentRange(final int offset, final int end,
         final int contentOffset, final int contentEndOffset,
         final CommentType type) {
      super();
      if (type == null) {
         throw new IllegalArgumentException("type is not allowed to be null");
      }
      this.beginOffset = offset;
      this.endOffset = end;
      this.contentBeginOffset = contentOffset;
      this.contentEndOffset = contentEndOffset;
      this.type = type;
   }

   /**
    * returns the inclusive Comments End Offset (including the closing signs of
    * Multiline Comments).
    *
    * @return the endOffset
    */
   public int getEndOffset() {
      return this.endOffset;
   }

   /**
    * returns the Comments Begin Offset (including the opening signs).
    *
    * @return the Begin Offset
    */
   public int getBeginOffset() {
      return this.beginOffset;
   }

   /**
    * returns the Comments Content Begin Offset.
    *
    * @return the inclusive Contents begin offset
    */
   public int getContentBeginOffset() {
      return this.contentBeginOffset;
   }

   /**
    * returns the Comment Contents End offset.
    *
    * @return the inclusive End Offset
    */
   public int getContentEndOffset() {
      return this.contentEndOffset;
   }

   /**
    * Returns the Comments length including Openers and Closers.
    *
    * @return the Comments length
    */
   public int getLength() {
      // Need to add one because end offset is inclusive
      return this.getEndOffset() - this.getBeginOffset() + 1;
   }

   /**
    * Returns the Contents length without openers and Closers.
    *
    * @return the contents length
    */
   public int getContentLength() {
      return this.getContentEndOffset() - this.getContentBeginOffset() + 1;
   }

   /**
    * Returns the type of the comment.
    *
    * @return the type
    */
   public CommentType getType() {
      return this.type;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getType() + 
             " (offset = " + getBeginOffset() + " to " + getEndOffset() +
             ", content offset = " + getContentBeginOffset() + " to " + getContentEndOffset() + ")";
   }
}
