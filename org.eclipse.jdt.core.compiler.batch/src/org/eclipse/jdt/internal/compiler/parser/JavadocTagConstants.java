/*******************************************************************************
 * Copyright (c) 2000, 2023 IBM Corporation and others.
 *
 * This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License 2.0
 * which accompanies this distribution, and is available at
 * https://www.eclipse.org/legal/epl-2.0/
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/

package org.eclipse.jdt.internal.compiler.parser;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import java.util.Objects;

/**
 * Javadoc tag constants.
 *
 * @since 3.2
 */
public interface JavadocTagConstants {

	// recognized tags
	public static final char[] TAG_DEPRECATED = "deprecated".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_PARAM = "param".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_RETURN = "return".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_THROWS = "throws".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_EXCEPTION = "exception".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_SEE = "see".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_LINK = "link".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_LINKPLAIN = "linkplain".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_INHERITDOC = "inheritDoc".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_VALUE = "value".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_AUTHOR = "author".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_CODE = "code".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_DOC_ROOT = "docRoot".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_LITERAL = "literal".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_SERIAL = "serial".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_SERIAL_DATA = "serialData".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_SERIAL_FIELD = "serialField".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_SINCE = "since".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_VERSION = "version".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_CATEGORY = "category".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_SYSTEM_PROPERTY = "systemProperty".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_USES = "uses".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_PROVIDES = "provides".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_HIDDEN = "hidden".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_INDEX = "index".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_SUMMARY = "summary".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_API_NOTE = "apiNote".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_IMPL_SPEC = "implSpec".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_IMPL_NOTE = "implNote".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_SNIPPET = "snippet".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_HIGHLIGHT = "highlight".toCharArray(); //$NON-NLS-1$
	public static final char[] TAG_REPLACE = "replace".toCharArray(); //$NON-NLS-1$

	// tags lengthes
	public static final int TAG_DEPRECATED_LENGTH = TAG_DEPRECATED.length;
	public static final int TAG_PARAM_LENGTH = TAG_PARAM.length;
	public static final int TAG_RETURN_LENGTH = TAG_RETURN.length;
	public static final int TAG_THROWS_LENGTH = TAG_THROWS.length;
	public static final int TAG_EXCEPTION_LENGTH = TAG_EXCEPTION.length;
	public static final int TAG_SEE_LENGTH = TAG_SEE.length;
	public static final int TAG_LINK_LENGTH = TAG_LINK.length;
	public static final int TAG_LINKPLAIN_LENGTH = TAG_LINKPLAIN.length;
	public static final int TAG_INHERITDOC_LENGTH = TAG_INHERITDOC.length;
	public static final int TAG_VALUE_LENGTH = TAG_VALUE.length;
	public static final int TAG_CATEGORY_LENGTH = TAG_CATEGORY.length;
	public static final int TAG_AUTHOR_LENGTH = TAG_AUTHOR.length;
	public static final int TAG_SERIAL_LENGTH = TAG_SERIAL.length;
	public static final int TAG_SERIAL_DATA_LENGTH = TAG_SERIAL_DATA.length;
	public static final int TAG_SERIAL_FIELD_LENGTH = TAG_SERIAL_FIELD.length;
	public static final int TAG_SINCE_LENGTH = TAG_SINCE.length;
	public static final int TAG_VERSION_LENGTH = TAG_VERSION.length;
	public static final int TAG_CODE_LENGTH = TAG_CODE.length;
	public static final int TAG_LITERAL_LENGTH = TAG_LITERAL.length;
	public static final int TAG_DOC_ROOT_LENGTH = TAG_DOC_ROOT.length;
	public static final int TAG_SYSTEM_PROPERTY_LENGTH = TAG_SYSTEM_PROPERTY.length;
	public static final int TAG_USES_LENGTH = TAG_USES.length;
	public static final int TAG_PROVIDES_LENGTH = TAG_PROVIDES.length;
	public static final int TAG_HIDDEN_LENGTH = TAG_HIDDEN.length;
	public static final int TAG_INDEX_LENGTH = TAG_INDEX.length;
	public static final int TAG_SUMMARY_LENGTH = TAG_SUMMARY.length;
	public static final int TAG_API_NOTE_LENGTH = TAG_API_NOTE.length;
	public static final int TAG_IMPL_SPEC_LENGTH = TAG_IMPL_SPEC.length;
	public static final int TAG_IMPL_NOTE_LENGTH = TAG_IMPL_NOTE.length;
	public static final int TAG_SNIPPET_LENGTH = TAG_SNIPPET.length;
	public static final int TAG_HIGHLIGHT_LENGTH = TAG_HIGHLIGHT.length;
	public static final int TAG_REPLACE_LENGTH = TAG_REPLACE.length;


	// tags value
	public static final int NO_TAG_VALUE = 0;
	public static final int TAG_DEPRECATED_VALUE = 1;
	public static final int TAG_PARAM_VALUE = 2;
	public static final int TAG_RETURN_VALUE = 3;
	public static final int TAG_THROWS_VALUE = 4;
	public static final int TAG_EXCEPTION_VALUE = 5;
	public static final int TAG_SEE_VALUE = 6;
	public static final int TAG_LINK_VALUE = 7;
	public static final int TAG_LINKPLAIN_VALUE = 8;
	public static final int TAG_INHERITDOC_VALUE = 9;
	public static final int TAG_VALUE_VALUE = 10;
	public static final int TAG_CATEGORY_VALUE = 11;
	public static final int TAG_AUTHOR_VALUE = 12;
	public static final int TAG_SERIAL_VALUE = 13;
	public static final int TAG_SERIAL_DATA_VALUE = 14;
	public static final int TAG_SERIAL_FIELD_VALUE = 15;
	public static final int TAG_SINCE_VALUE = 16;
	public static final int TAG_VERSION_VALUE = 17;
	public static final int TAG_CODE_VALUE = 18;
	public static final int TAG_LITERAL_VALUE = 19;
	public static final int TAG_DOC_ROOT_VALUE = 20;
	public static final int TAG_SYSTEM_PROPERTY_VALUE=21;
	public static final int TAG_USES_VALUE=22;
	public static final int TAG_PROVIDES_VALUE=23;
	public static final int TAG_HIDDEN_VALUE = 24;
	public static final int TAG_INDEX_VALUE = 25;
	public static final int TAG_SUMMARY_VALUE = 26;
	public static final int TAG_API_NOTE_VALUE = 27;
	public static final int TAG_IMPL_SPEC_VALUE = 28;
	public static final int TAG_IMPL_NOTE_VALUE = 29;
	public static final int TAG_SNIPPET_VALUE = 30;
	public static final int TAG_HIGHLIGHT_VALUE = 31;
	public static final int TAG_REPLACE_VALUE = 32;
	public static final int TAG_OTHERS_VALUE = 100;
	// Tag names array
	public static final char[][] TAG_NAMES = {
		CharOperation.NO_CHAR,
		TAG_DEPRECATED,		/* 1 */
		TAG_PARAM,				/* 2 */
		TAG_RETURN,				/* 3 */
		TAG_THROWS,				/* 4 */
		TAG_EXCEPTION,			/* 5 */
		TAG_SEE,						/* 6 */
		TAG_LINK,						/* 7 */
		TAG_LINKPLAIN,			/* 8 */
		TAG_INHERITDOC,		/* 9 */
		TAG_VALUE,					/* 10 */
		TAG_CATEGORY,			/* 11 */
		TAG_AUTHOR,				/* 12 */
		TAG_SERIAL,				/* 13 */
		TAG_SERIAL_DATA,	/* 14 */
		TAG_SERIAL_FIELD,	/* 15 */
		TAG_SINCE,					/* 16 */
		TAG_VERSION,				/* 17 */
		TAG_CODE,					/* 18 */
		TAG_LITERAL,				/* 19 */
		TAG_DOC_ROOT,			/* 20 */
		TAG_SYSTEM_PROPERTY,    /* 21 */
		TAG_USES,				/* 22 */
		TAG_PROVIDES,			/* 23 */
		TAG_HIDDEN,				/* 24 */
		TAG_INDEX,				/* 25 */
		TAG_SUMMARY,			/* 26 */
		TAG_API_NOTE,			/* 27 */
		TAG_IMPL_SPEC,			/* 28 */
		TAG_IMPL_NOTE,			/* 29 */
		TAG_SNIPPET,			/* 30 */
		TAG_HIGHLIGHT,			/* 31 */
		TAG_REPLACE,			/* 32 */
	};

	// tags expected positions
	public final static int ORDERED_TAGS_NUMBER = 3;
	public final static int PARAM_TAG_EXPECTED_ORDER = 0;
	public final static int THROWS_TAG_EXPECTED_ORDER = 1;
	public final static int SEE_TAG_EXPECTED_ORDER = 2;

	/*
	 * Tag kinds indexes
	 */
	public final static int BLOCK_IDX = 0;
	public final static int INLINE_IDX = 1;
	public final static int SNIPPET_IDX = 2;


	// href tag
	public final static char[] HREF_TAG = {'h', 'r', 'e', 'f'};

	/**
	 * A record class representing additional tags to be made
	 * available at specific java version levels.
	 *
	 * This class is intended to prevent maintainers from having to add
	 * empty arrays for each new java version that is released.
	 */
	class LevelTags
    {
        public final int level;
        public final char[][] tags;

        public LevelTags(int level, char[][] tags) {
            this.level = level;
            this.tags = tags;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (!(o instanceof LevelTags)) {
                return false;
            }
            LevelTags levelTags = (LevelTags) o;
            return Integer.compare(this.level, levelTags.level) == 0 && Objects.equals(this.tags, levelTags.tags);
        }

        @Override
        public int hashCode() {
            return Objects.hash(this.level, this.tags);
        }
    }
	/**
	 * Convert an array of LevelTags into the char[][][] structure that is currently used to
	 * discover the additional tags available at a given java version.
	 *
	 * @param input A LevelTags array representing additional tags available for each java version
	 * @return a char[][][] array representing newly available tags for all java class version
	 */
	public static char[][][] levelTagsToChar3d(LevelTags[] input) {
		int expectedLength = ClassFileConstants.MAJOR_LATEST_VERSION - ClassFileConstants.MAJOR_VERSION_0 + 1;
		char[][][] ret = new char[expectedLength][][];
		for( int i = 0; i < ret.length; i++ ) {
			ret[i] = new char[][] {};
		}
		for( int i = 0; i < input.length; i++ ) {
			int nextLevel = input[i].level - ClassFileConstants.MAJOR_VERSION_0;
			ret[nextLevel] = input[i].tags;
		}
		return ret;
	}

	/*
	 * Tags versions
	 *
	 * Maintainers should add a new LevelTag only for versions in which new tags are made available
	 */
	public static final LevelTags[] BLOCK_TAGS_RAW = {
		new LevelTags(ClassFileConstants.MAJOR_VERSION_0, new char[][]{ TAG_AUTHOR, TAG_DEPRECATED, TAG_EXCEPTION, TAG_PARAM, TAG_RETURN, TAG_SEE, TAG_VERSION, TAG_CATEGORY /* 1.6 tag but put here as we support it for all compliances */ }),
		new LevelTags(ClassFileConstants.MAJOR_VERSION_1_1, new char[][]{ TAG_SINCE }),
		new LevelTags(ClassFileConstants.MAJOR_VERSION_1_2, new char[][]{ TAG_SERIAL, TAG_SERIAL_DATA, TAG_SERIAL_FIELD , TAG_THROWS }),
		new LevelTags(ClassFileConstants.MAJOR_VERSION_1_8, new char[][]{TAG_API_NOTE, TAG_IMPL_SPEC, TAG_IMPL_NOTE}),
		new LevelTags(ClassFileConstants.MAJOR_VERSION_9, new char[][]{ TAG_HIDDEN, TAG_USES, TAG_PROVIDES })
	};
	public static final char[][][] BLOCK_TAGS = levelTagsToChar3d(BLOCK_TAGS_RAW);

	/*
	 * Inline Tags versions
	 *
	 * Maintainers should add a new LevelTag only for versions in which new tags are made available
	 */
	public static final LevelTags[] INLINE_TAGS_RAW = {
			new LevelTags(ClassFileConstants.MAJOR_VERSION_1_2, new char[][]{ TAG_LINK }),
			new LevelTags(ClassFileConstants.MAJOR_VERSION_1_3, new char[][]{ TAG_DOC_ROOT }),
			new LevelTags(ClassFileConstants.MAJOR_VERSION_1_4, new char[][]{ TAG_INHERITDOC, TAG_LINKPLAIN, TAG_VALUE }),
			new LevelTags(ClassFileConstants.MAJOR_VERSION_1_5, new char[][]{ TAG_CODE, TAG_LITERAL }),
			new LevelTags(ClassFileConstants.MAJOR_VERSION_9, new char[][]{ TAG_INDEX }),
			new LevelTags(ClassFileConstants.MAJOR_VERSION_10, new char[][]{ TAG_SUMMARY }),
			new LevelTags(ClassFileConstants.MAJOR_VERSION_12, new char[][]{ TAG_SYSTEM_PROPERTY }),
			new LevelTags(ClassFileConstants.MAJOR_VERSION_16, new char[][]{ TAG_RETURN }),
			new LevelTags(ClassFileConstants.MAJOR_VERSION_18, new char[][]{ TAG_SNIPPET }),
		};
	public static final char[][][] INLINE_TAGS = levelTagsToChar3d(INLINE_TAGS_RAW);



	public static final char[][][] IN_SNIPPET_TAGS = {
		//since 18
			{ TAG_HIGHLIGHT, TAG_REPLACE, TAG_LINK }
	};
	public final static int IN_SNIPPET_TAGS_LENGTH = IN_SNIPPET_TAGS.length;
	public final static int INLINE_TAGS_LENGTH = INLINE_TAGS.length;
	public final static int SNIPPET_TAGS_LENGTH = IN_SNIPPET_TAGS.length;

	public final static int BLOCK_TAGS_LENGTH = BLOCK_TAGS.length;
	public final static int ALL_TAGS_LENGTH = BLOCK_TAGS_LENGTH+INLINE_TAGS_LENGTH;

	public final static short TAG_TYPE_NONE = 0;
	public final static short TAG_TYPE_INLINE = 1;
	public final static short TAG_TYPE_BLOCK = 2;
	public final static short TAG_TYPE_IN_SNIPPET = 4;
	public final static short TAG_TYPE_INLINE_BLOCK = (short) (TAG_TYPE_INLINE | TAG_TYPE_BLOCK);
	public static final short[] JAVADOC_TAG_TYPE = {
			TAG_TYPE_NONE, 		// NO_TAG_VALUE = 0;
			TAG_TYPE_BLOCK,		// TAG_DEPRECATED_VALUE = 1;
			TAG_TYPE_BLOCK,		// TAG_PARAM_VALUE = 2;
			TAG_TYPE_BLOCK,		// TAG_RETURN_VALUE = 3;
			TAG_TYPE_BLOCK,		// TAG_THROWS_VALUE = 4;
			TAG_TYPE_BLOCK,		// TAG_EXCEPTION_VALUE = 5;
			TAG_TYPE_BLOCK,		// TAG_SEE_VALUE = 6;
			TAG_TYPE_INLINE,	// TAG_LINK_VALUE = 7;
			TAG_TYPE_INLINE,	// TAG_LINKPLAIN_VALUE = 8;
			TAG_TYPE_INLINE,	// TAG_INHERITDOC_VALUE = 9;
			TAG_TYPE_INLINE,	// TAG_VALUE_VALUE = 10;
			TAG_TYPE_BLOCK,		// TAG_CATEGORY_VALUE = 11;
			TAG_TYPE_BLOCK,		// TAG_AUTHOR_VALUE = 12;
			TAG_TYPE_BLOCK,		// TAG_SERIAL_VALUE = 13;
			TAG_TYPE_BLOCK,		// TAG_SERIAL_DATA_VALUE = 14;
			TAG_TYPE_BLOCK,		// TAG_SERIAL_FIELD_VALUE = 15;
			TAG_TYPE_BLOCK,		// TAG_SINCE_VALUE = 16;
			TAG_TYPE_BLOCK,		// TAG_VERSION_VALUE = 17;
			TAG_TYPE_INLINE,	// TAG_CODE_VALUE = 18;
			TAG_TYPE_INLINE,	// TAG_LITERAL_VALUE = 19;
			TAG_TYPE_INLINE,	// TAG_DOC_ROOT_VALUE = 20;
			TAG_TYPE_INLINE,    // TAG_DOC_SYSTEM_PROPERTY = 21
			TAG_TYPE_BLOCK,		// TAG_USES_VALUE = 22;
			TAG_TYPE_BLOCK,		// TAG_PROVIDES_VALUE = 23;
			TAG_TYPE_BLOCK,		// TAG_HIDDEN_VALUE = 24;
			TAG_TYPE_INLINE,	// TAG_INDEX_VALUE = 25;
			TAG_TYPE_INLINE,	// TAG_SUMMARY_VALUE = 26;
			TAG_TYPE_BLOCK,		// TAG_API_NOTE = 27;
			TAG_TYPE_BLOCK,		// TAG_IMPL_SPEC = 28;
			TAG_TYPE_BLOCK,		// TAG_IMPL_NOTE = 29;
			TAG_TYPE_INLINE,	// TAG_SNIPPET_VALUE = 30;
			TAG_TYPE_IN_SNIPPET,// TAG_HIGHLIGHT_VALUE = 31;
			TAG_TYPE_IN_SNIPPET,// TAG_HIGHLIGHT_VALUE = 32;
	 	};
	// Same as above with a single difference for TAG_RETURN_VALUE
	// which can now be both TAG_TYPE_BLOCK and TAG_TYPE_INLINE => TAG_TYPE_INLINE_BLOCK
	// Should this become complex, meaning multiple JLS levels requiring different support,
	// we will need a better model to capture that. For now, this should be enough.
	public static final short[] JAVADOC_TAG_TYPE_16PLUS = {
		TAG_TYPE_NONE, 		// NO_TAG_VALUE = 0;
		TAG_TYPE_BLOCK,		// TAG_DEPRECATED_VALUE = 1;
		TAG_TYPE_BLOCK,		// TAG_PARAM_VALUE = 2;
		TAG_TYPE_INLINE_BLOCK,		// TAG_RETURN_VALUE = 3;
		TAG_TYPE_BLOCK,		// TAG_THROWS_VALUE = 4;
		TAG_TYPE_BLOCK,		// TAG_EXCEPTION_VALUE = 5;
		TAG_TYPE_BLOCK,		// TAG_SEE_VALUE = 6;
		TAG_TYPE_INLINE,	// TAG_LINK_VALUE = 7;
		TAG_TYPE_INLINE,	// TAG_LINKPLAIN_VALUE = 8;
		TAG_TYPE_INLINE,	// TAG_INHERITDOC_VALUE = 9;
		TAG_TYPE_INLINE,	// TAG_VALUE_VALUE = 10;
		TAG_TYPE_BLOCK,		// TAG_CATEGORY_VALUE = 11;
		TAG_TYPE_BLOCK,		// TAG_AUTHOR_VALUE = 12;
		TAG_TYPE_BLOCK,		// TAG_SERIAL_VALUE = 13;
		TAG_TYPE_BLOCK,		// TAG_SERIAL_DATA_VALUE = 14;
		TAG_TYPE_BLOCK,		// TAG_SERIAL_FIELD_VALUE = 15;
		TAG_TYPE_BLOCK,		// TAG_SINCE_VALUE = 16;
		TAG_TYPE_BLOCK,		// TAG_VERSION_VALUE = 17;
		TAG_TYPE_INLINE,	// TAG_CODE_VALUE = 18;
		TAG_TYPE_INLINE,	// TAG_LITERAL_VALUE = 19;
		TAG_TYPE_INLINE,	// TAG_DOC_ROOT_VALUE = 20;
		TAG_TYPE_INLINE,    // TAG_DOC_SYSTEM_PROPERTY = 21
		TAG_TYPE_BLOCK,		// TAG_USES_VALUE = 22;
		TAG_TYPE_BLOCK,		// TAG_PROVIDES_VALUE = 23;
		TAG_TYPE_BLOCK,		// TAG_HIDDEN_VALUE = 24;
		TAG_TYPE_INLINE,	// TAG_INDEX_VALUE = 25;
		TAG_TYPE_INLINE,	// TAG_SUMMARY_VALUE = 26;
		TAG_TYPE_BLOCK,		// TAG_API_NOTE = 27;
		TAG_TYPE_BLOCK,		// TAG_IMPL_SPEC = 28;
		TAG_TYPE_BLOCK,		// TAG_IMPL_NOTE = 29;
		TAG_TYPE_INLINE,	// TAG_SNIPPET_VALUE = 30;
		TAG_TYPE_IN_SNIPPET,// TAG_HIGHLIGHT_VALUE = 31;
		TAG_TYPE_IN_SNIPPET,// TAG_HIGHLIGHT_VALUE = 32;
 	};
	/*
	 * Tags usage
	 */
	public static final char[][] PACKAGE_TAGS = {
		TAG_SEE,
		TAG_SINCE,
		TAG_SERIAL,
		TAG_AUTHOR,
		TAG_VERSION,
		TAG_CATEGORY,
		TAG_LINK,
		TAG_LINKPLAIN,
		TAG_DOC_ROOT,
		TAG_VALUE,
		TAG_SYSTEM_PROPERTY,
		TAG_HIDDEN,
		TAG_INDEX,
		TAG_SUMMARY,
		TAG_API_NOTE,
		TAG_IMPL_SPEC,
		TAG_IMPL_NOTE,
		TAG_SNIPPET,
		TAG_HIGHLIGHT,
		TAG_REPLACE
	};
	public static final char[][] COMPILATION_UNIT_TAGS = {};
	public static final char[][] CLASS_TAGS = {
		TAG_SEE,
		TAG_SINCE,
		TAG_DEPRECATED,
		TAG_SERIAL,
		TAG_AUTHOR,
		TAG_VERSION,
		TAG_PARAM,
		TAG_CATEGORY,
		TAG_LINK,
		TAG_LINKPLAIN,
		TAG_DOC_ROOT,
		TAG_VALUE,
		TAG_CODE,
		TAG_LITERAL,
		TAG_SYSTEM_PROPERTY,
		TAG_HIDDEN,
		TAG_INDEX,
		TAG_SUMMARY,
		TAG_API_NOTE,
		TAG_IMPL_SPEC,
		TAG_IMPL_NOTE,
		TAG_SNIPPET,
		TAG_HIGHLIGHT,
		TAG_REPLACE
	};
	public static final char[][] FIELD_TAGS = {
		TAG_SEE,
		TAG_SINCE,
		TAG_DEPRECATED,
		TAG_SERIAL,
		TAG_SERIAL_FIELD,
		TAG_CATEGORY,
		TAG_LINK,
		TAG_LINKPLAIN,
		TAG_DOC_ROOT,
		TAG_VALUE,
		TAG_CODE,
		TAG_LITERAL,
		TAG_SYSTEM_PROPERTY,
		TAG_INDEX,
		TAG_HIDDEN,
		TAG_SUMMARY,
		TAG_API_NOTE,
		TAG_IMPL_SPEC,
		TAG_IMPL_NOTE,
		TAG_SNIPPET,
		TAG_HIGHLIGHT,
		TAG_REPLACE
	};
	public static final char[][] METHOD_TAGS = {
		TAG_SEE,
		TAG_SINCE,
		TAG_DEPRECATED,
		TAG_PARAM,
		TAG_RETURN,
		TAG_THROWS,
		TAG_EXCEPTION,
		TAG_SERIAL_DATA,
		TAG_CATEGORY,
		TAG_LINK,
		TAG_LINKPLAIN,
		TAG_INHERITDOC,
		TAG_DOC_ROOT,
		TAG_VALUE,
		TAG_CODE,
		TAG_LITERAL,
		TAG_SYSTEM_PROPERTY,
		TAG_HIDDEN,
		TAG_INDEX,
		TAG_SUMMARY,
		TAG_API_NOTE,
		TAG_IMPL_SPEC,
		TAG_IMPL_NOTE,
		TAG_SNIPPET,
		TAG_HIGHLIGHT,
		TAG_REPLACE
	};
	public static final char[][] MODULE_TAGS = {
			TAG_SEE,
			TAG_SINCE,
			TAG_DEPRECATED,
			TAG_SERIAL,
			TAG_AUTHOR,
			TAG_VERSION,
			TAG_CATEGORY,
			TAG_LINK,
			TAG_LINKPLAIN,
			TAG_DOC_ROOT,
			TAG_VALUE,
			TAG_CODE,
			TAG_LITERAL,
			TAG_USES,
			TAG_PROVIDES,
			TAG_HIDDEN,
			TAG_INDEX,
			TAG_SUMMARY,
			TAG_API_NOTE,
			TAG_IMPL_SPEC,
			TAG_IMPL_NOTE,
			TAG_SNIPPET,
			TAG_HIGHLIGHT,
			TAG_REPLACE
		};
}
