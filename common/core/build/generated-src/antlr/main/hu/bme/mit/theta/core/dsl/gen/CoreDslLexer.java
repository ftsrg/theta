// Generated from CoreDsl.g4 by ANTLR 4.7.2
package hu.bme.mit.theta.core.dsl.gen;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class CoreDslLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.7.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		BOOLTYPE=1, INTTYPE=2, RATTYPE=3, BVTYPE=4, IF=5, THEN=6, ELSE=7, IFF=8, 
		IMPLY=9, FORALL=10, EXISTS=11, OR=12, AND=13, NOT=14, EQ=15, NEQ=16, LT=17, 
		LEQ=18, GT=19, GEQ=20, PLUS=21, MINUS=22, MUL=23, DIV=24, MOD=25, REM=26, 
		PERCENT=27, BV_ADD=28, BV_SUB=29, BV_POS=30, BV_NEG=31, BV_MUL=32, BV_UDIV=33, 
		BV_SDIV=34, BV_SMOD=35, BV_UREM=36, BV_SREM=37, BV_OR=38, BV_AND=39, BV_XOR=40, 
		BV_NOT=41, BV_SHL=42, BV_ASHR=43, BV_LSHR=44, BV_ROL=45, BV_ROR=46, BV_ULT=47, 
		BV_ULE=48, BV_UGT=49, BV_UGE=50, BV_SLT=51, BV_SLE=52, BV_SGT=53, BV_SGE=54, 
		BV_CONCAT=55, BV_ZERO_EXTEND=56, BV_SIGN_EXTEND=57, TRUE=58, FALSE=59, 
		ASSIGN=60, HAVOC=61, ASSUME=62, BV=63, INT=64, NAT=65, SIGN=66, DOT=67, 
		ID=68, UNDERSCORE=69, DIGIT=70, LETTER=71, LPAREN=72, RPAREN=73, LBRACK=74, 
		RBRACK=75, LBRAC=76, RBRAC=77, COMMA=78, COLON=79, SEMICOLON=80, QUOT=81, 
		LARROW=82, RARROW=83, WS=84, COMMENT=85, LINE_COMMENT=86;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"BOOLTYPE", "INTTYPE", "RATTYPE", "BVTYPE", "IF", "THEN", "ELSE", "IFF", 
			"IMPLY", "FORALL", "EXISTS", "OR", "AND", "NOT", "EQ", "NEQ", "LT", "LEQ", 
			"GT", "GEQ", "PLUS", "MINUS", "MUL", "DIV", "MOD", "REM", "PERCENT", 
			"BV_ADD", "BV_SUB", "BV_POS", "BV_NEG", "BV_MUL", "BV_UDIV", "BV_SDIV", 
			"BV_SMOD", "BV_UREM", "BV_SREM", "BV_OR", "BV_AND", "BV_XOR", "BV_NOT", 
			"BV_SHL", "BV_ASHR", "BV_LSHR", "BV_ROL", "BV_ROR", "BV_ULT", "BV_ULE", 
			"BV_UGT", "BV_UGE", "BV_SLT", "BV_SLE", "BV_SGT", "BV_SGE", "BV_CONCAT", 
			"BV_ZERO_EXTEND", "BV_SIGN_EXTEND", "TRUE", "FALSE", "ASSIGN", "HAVOC", 
			"ASSUME", "BV", "INT", "NAT", "SIGN", "DOT", "ID", "UNDERSCORE", "DIGIT", 
			"LETTER", "LPAREN", "RPAREN", "LBRACK", "RBRACK", "LBRAC", "RBRAC", "COMMA", 
			"COLON", "SEMICOLON", "QUOT", "LARROW", "RARROW", "WS", "COMMENT", "LINE_COMMENT"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'bool'", "'int'", "'rat'", "'bv'", "'if'", "'then'", "'else'", 
			"'iff'", "'imply'", "'forall'", "'exists'", "'or'", "'and'", "'not'", 
			"'='", "'/='", "'<'", "'<='", "'>'", "'>='", "'+'", "'-'", "'*'", "'/'", 
			"'mod'", "'rem'", "'%'", "'bvadd'", "'bvsub'", "'bvpos'", "'bvneg'", 
			"'bvmul'", "'bvudiv'", "'bvsdiv'", "'bvsmod'", "'bvurem'", "'bvsrem'", 
			"'bvor'", "'bvand'", "'bvxor'", "'bvnot'", "'bvshl'", "'bvashr'", "'bvlshr'", 
			"'bvrol'", "'bvror'", "'bvult'", "'bvule'", "'bvugt'", "'bvuge'", "'bvslt'", 
			"'bvsle'", "'bvsgt'", "'bvsge'", null, "'bv_zero_extend'", "'bv_sign_extend'", 
			"'true'", "'false'", "':='", "'havoc'", "'assume'", null, null, null, 
			null, "'.'", null, "'_'", null, null, "'('", "')'", "'['", "']'", "'{'", 
			"'}'", "','", "':'", "';'", "'''", "'<-'", "'->'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "BOOLTYPE", "INTTYPE", "RATTYPE", "BVTYPE", "IF", "THEN", "ELSE", 
			"IFF", "IMPLY", "FORALL", "EXISTS", "OR", "AND", "NOT", "EQ", "NEQ", 
			"LT", "LEQ", "GT", "GEQ", "PLUS", "MINUS", "MUL", "DIV", "MOD", "REM", 
			"PERCENT", "BV_ADD", "BV_SUB", "BV_POS", "BV_NEG", "BV_MUL", "BV_UDIV", 
			"BV_SDIV", "BV_SMOD", "BV_UREM", "BV_SREM", "BV_OR", "BV_AND", "BV_XOR", 
			"BV_NOT", "BV_SHL", "BV_ASHR", "BV_LSHR", "BV_ROL", "BV_ROR", "BV_ULT", 
			"BV_ULE", "BV_UGT", "BV_UGE", "BV_SLT", "BV_SLE", "BV_SGT", "BV_SGE", 
			"BV_CONCAT", "BV_ZERO_EXTEND", "BV_SIGN_EXTEND", "TRUE", "FALSE", "ASSIGN", 
			"HAVOC", "ASSUME", "BV", "INT", "NAT", "SIGN", "DOT", "ID", "UNDERSCORE", 
			"DIGIT", "LETTER", "LPAREN", "RPAREN", "LBRACK", "RBRACK", "LBRAC", "RBRAC", 
			"COMMA", "COLON", "SEMICOLON", "QUOT", "LARROW", "RARROW", "WS", "COMMENT", 
			"LINE_COMMENT"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	public CoreDslLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "CoreDsl.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2X\u026b\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\4A\tA\4B\tB\4C\tC\4D\tD\4E\tE\4F\tF\4G\tG\4H\tH\4I"+
		"\tI\4J\tJ\4K\tK\4L\tL\4M\tM\4N\tN\4O\tO\4P\tP\4Q\tQ\4R\tR\4S\tS\4T\tT"+
		"\4U\tU\4V\tV\4W\tW\3\2\3\2\3\2\3\2\3\2\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4"+
		"\3\5\3\5\3\5\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\t\3"+
		"\t\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\13\3\13\3\13"+
		"\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\17\3\17"+
		"\3\17\3\17\3\20\3\20\3\21\3\21\3\21\3\22\3\22\3\23\3\23\3\23\3\24\3\24"+
		"\3\25\3\25\3\25\3\26\3\26\3\27\3\27\3\30\3\30\3\31\3\31\3\32\3\32\3\32"+
		"\3\32\3\33\3\33\3\33\3\33\3\34\3\34\3\35\3\35\3\35\3\35\3\35\3\35\3\36"+
		"\3\36\3\36\3\36\3\36\3\36\3\37\3\37\3\37\3\37\3\37\3\37\3 \3 \3 \3 \3"+
		" \3 \3!\3!\3!\3!\3!\3!\3\"\3\"\3\"\3\"\3\"\3\"\3\"\3#\3#\3#\3#\3#\3#\3"+
		"#\3$\3$\3$\3$\3$\3$\3$\3%\3%\3%\3%\3%\3%\3%\3&\3&\3&\3&\3&\3&\3&\3\'\3"+
		"\'\3\'\3\'\3\'\3(\3(\3(\3(\3(\3(\3)\3)\3)\3)\3)\3)\3*\3*\3*\3*\3*\3*\3"+
		"+\3+\3+\3+\3+\3+\3,\3,\3,\3,\3,\3,\3,\3-\3-\3-\3-\3-\3-\3-\3.\3.\3.\3"+
		".\3.\3.\3/\3/\3/\3/\3/\3/\3\60\3\60\3\60\3\60\3\60\3\60\3\61\3\61\3\61"+
		"\3\61\3\61\3\61\3\62\3\62\3\62\3\62\3\62\3\62\3\63\3\63\3\63\3\63\3\63"+
		"\3\63\3\64\3\64\3\64\3\64\3\64\3\64\3\65\3\65\3\65\3\65\3\65\3\65\3\66"+
		"\3\66\3\66\3\66\3\66\3\66\3\67\3\67\3\67\3\67\3\67\3\67\38\38\38\39\3"+
		"9\39\39\39\39\39\39\39\39\39\39\39\39\39\3:\3:\3:\3:\3:\3:\3:\3:\3:\3"+
		":\3:\3:\3:\3:\3:\3;\3;\3;\3;\3;\3<\3<\3<\3<\3<\3<\3=\3=\3=\3>\3>\3>\3"+
		">\3>\3>\3?\3?\3?\3?\3?\3?\3?\3@\3@\3@\3@\3@\6@\u01fa\n@\r@\16@\u01fb\3"+
		"@\3@\3@\3@\3@\3@\5@\u0204\n@\3@\3@\3@\3@\3@\3@\3@\6@\u020d\n@\r@\16@\u020e"+
		"\5@\u0211\n@\3A\3A\3B\6B\u0216\nB\rB\16B\u0217\3C\3C\5C\u021c\nC\3D\3"+
		"D\3E\3E\5E\u0222\nE\3E\3E\3E\7E\u0227\nE\fE\16E\u022a\13E\3F\3F\3G\3G"+
		"\3H\3H\3I\3I\3J\3J\3K\3K\3L\3L\3M\3M\3N\3N\3O\3O\3P\3P\3Q\3Q\3R\3R\3S"+
		"\3S\3S\3T\3T\3T\3U\6U\u024d\nU\rU\16U\u024e\3U\3U\3V\3V\3V\3V\7V\u0257"+
		"\nV\fV\16V\u025a\13V\3V\3V\3V\3V\3V\3W\3W\3W\3W\7W\u0265\nW\fW\16W\u0268"+
		"\13W\3W\3W\3\u0258\2X\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27"+
		"\r\31\16\33\17\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33"+
		"\65\34\67\359\36;\37= ?!A\"C#E$G%I&K\'M(O)Q*S+U,W-Y.[/]\60_\61a\62c\63"+
		"e\64g\65i\66k\67m8o9q:s;u<w=y>{?}@\177A\u0081B\u0083C\u0085D\u0087E\u0089"+
		"F\u008bG\u008dH\u008fI\u0091J\u0093K\u0095L\u0097M\u0099N\u009bO\u009d"+
		"P\u009fQ\u00a1R\u00a3S\u00a5T\u00a7U\u00a9V\u00abW\u00adX\3\2\b\3\2\62"+
		"\63\5\2\62;CHch\3\2\62;\4\2C\\c|\5\2\13\f\16\17\"\"\4\2\f\f\17\17\2\u0279"+
		"\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2"+
		"\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2"+
		"\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2"+
		"\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2"+
		"\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3"+
		"\2\2\2\2=\3\2\2\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2"+
		"\2\2I\3\2\2\2\2K\3\2\2\2\2M\3\2\2\2\2O\3\2\2\2\2Q\3\2\2\2\2S\3\2\2\2\2"+
		"U\3\2\2\2\2W\3\2\2\2\2Y\3\2\2\2\2[\3\2\2\2\2]\3\2\2\2\2_\3\2\2\2\2a\3"+
		"\2\2\2\2c\3\2\2\2\2e\3\2\2\2\2g\3\2\2\2\2i\3\2\2\2\2k\3\2\2\2\2m\3\2\2"+
		"\2\2o\3\2\2\2\2q\3\2\2\2\2s\3\2\2\2\2u\3\2\2\2\2w\3\2\2\2\2y\3\2\2\2\2"+
		"{\3\2\2\2\2}\3\2\2\2\2\177\3\2\2\2\2\u0081\3\2\2\2\2\u0083\3\2\2\2\2\u0085"+
		"\3\2\2\2\2\u0087\3\2\2\2\2\u0089\3\2\2\2\2\u008b\3\2\2\2\2\u008d\3\2\2"+
		"\2\2\u008f\3\2\2\2\2\u0091\3\2\2\2\2\u0093\3\2\2\2\2\u0095\3\2\2\2\2\u0097"+
		"\3\2\2\2\2\u0099\3\2\2\2\2\u009b\3\2\2\2\2\u009d\3\2\2\2\2\u009f\3\2\2"+
		"\2\2\u00a1\3\2\2\2\2\u00a3\3\2\2\2\2\u00a5\3\2\2\2\2\u00a7\3\2\2\2\2\u00a9"+
		"\3\2\2\2\2\u00ab\3\2\2\2\2\u00ad\3\2\2\2\3\u00af\3\2\2\2\5\u00b4\3\2\2"+
		"\2\7\u00b8\3\2\2\2\t\u00bc\3\2\2\2\13\u00bf\3\2\2\2\r\u00c2\3\2\2\2\17"+
		"\u00c7\3\2\2\2\21\u00cc\3\2\2\2\23\u00d0\3\2\2\2\25\u00d6\3\2\2\2\27\u00dd"+
		"\3\2\2\2\31\u00e4\3\2\2\2\33\u00e7\3\2\2\2\35\u00eb\3\2\2\2\37\u00ef\3"+
		"\2\2\2!\u00f1\3\2\2\2#\u00f4\3\2\2\2%\u00f6\3\2\2\2\'\u00f9\3\2\2\2)\u00fb"+
		"\3\2\2\2+\u00fe\3\2\2\2-\u0100\3\2\2\2/\u0102\3\2\2\2\61\u0104\3\2\2\2"+
		"\63\u0106\3\2\2\2\65\u010a\3\2\2\2\67\u010e\3\2\2\29\u0110\3\2\2\2;\u0116"+
		"\3\2\2\2=\u011c\3\2\2\2?\u0122\3\2\2\2A\u0128\3\2\2\2C\u012e\3\2\2\2E"+
		"\u0135\3\2\2\2G\u013c\3\2\2\2I\u0143\3\2\2\2K\u014a\3\2\2\2M\u0151\3\2"+
		"\2\2O\u0156\3\2\2\2Q\u015c\3\2\2\2S\u0162\3\2\2\2U\u0168\3\2\2\2W\u016e"+
		"\3\2\2\2Y\u0175\3\2\2\2[\u017c\3\2\2\2]\u0182\3\2\2\2_\u0188\3\2\2\2a"+
		"\u018e\3\2\2\2c\u0194\3\2\2\2e\u019a\3\2\2\2g\u01a0\3\2\2\2i\u01a6\3\2"+
		"\2\2k\u01ac\3\2\2\2m\u01b2\3\2\2\2o\u01b8\3\2\2\2q\u01bb\3\2\2\2s\u01ca"+
		"\3\2\2\2u\u01d9\3\2\2\2w\u01de\3\2\2\2y\u01e4\3\2\2\2{\u01e7\3\2\2\2}"+
		"\u01ed\3\2\2\2\177\u0210\3\2\2\2\u0081\u0212\3\2\2\2\u0083\u0215\3\2\2"+
		"\2\u0085\u021b\3\2\2\2\u0087\u021d\3\2\2\2\u0089\u0221\3\2\2\2\u008b\u022b"+
		"\3\2\2\2\u008d\u022d\3\2\2\2\u008f\u022f\3\2\2\2\u0091\u0231\3\2\2\2\u0093"+
		"\u0233\3\2\2\2\u0095\u0235\3\2\2\2\u0097\u0237\3\2\2\2\u0099\u0239\3\2"+
		"\2\2\u009b\u023b\3\2\2\2\u009d\u023d\3\2\2\2\u009f\u023f\3\2\2\2\u00a1"+
		"\u0241\3\2\2\2\u00a3\u0243\3\2\2\2\u00a5\u0245\3\2\2\2\u00a7\u0248\3\2"+
		"\2\2\u00a9\u024c\3\2\2\2\u00ab\u0252\3\2\2\2\u00ad\u0260\3\2\2\2\u00af"+
		"\u00b0\7d\2\2\u00b0\u00b1\7q\2\2\u00b1\u00b2\7q\2\2\u00b2\u00b3\7n\2\2"+
		"\u00b3\4\3\2\2\2\u00b4\u00b5\7k\2\2\u00b5\u00b6\7p\2\2\u00b6\u00b7\7v"+
		"\2\2\u00b7\6\3\2\2\2\u00b8\u00b9\7t\2\2\u00b9\u00ba\7c\2\2\u00ba\u00bb"+
		"\7v\2\2\u00bb\b\3\2\2\2\u00bc\u00bd\7d\2\2\u00bd\u00be\7x\2\2\u00be\n"+
		"\3\2\2\2\u00bf\u00c0\7k\2\2\u00c0\u00c1\7h\2\2\u00c1\f\3\2\2\2\u00c2\u00c3"+
		"\7v\2\2\u00c3\u00c4\7j\2\2\u00c4\u00c5\7g\2\2\u00c5\u00c6\7p\2\2\u00c6"+
		"\16\3\2\2\2\u00c7\u00c8\7g\2\2\u00c8\u00c9\7n\2\2\u00c9\u00ca\7u\2\2\u00ca"+
		"\u00cb\7g\2\2\u00cb\20\3\2\2\2\u00cc\u00cd\7k\2\2\u00cd\u00ce\7h\2\2\u00ce"+
		"\u00cf\7h\2\2\u00cf\22\3\2\2\2\u00d0\u00d1\7k\2\2\u00d1\u00d2\7o\2\2\u00d2"+
		"\u00d3\7r\2\2\u00d3\u00d4\7n\2\2\u00d4\u00d5\7{\2\2\u00d5\24\3\2\2\2\u00d6"+
		"\u00d7\7h\2\2\u00d7\u00d8\7q\2\2\u00d8\u00d9\7t\2\2\u00d9\u00da\7c\2\2"+
		"\u00da\u00db\7n\2\2\u00db\u00dc\7n\2\2\u00dc\26\3\2\2\2\u00dd\u00de\7"+
		"g\2\2\u00de\u00df\7z\2\2\u00df\u00e0\7k\2\2\u00e0\u00e1\7u\2\2\u00e1\u00e2"+
		"\7v\2\2\u00e2\u00e3\7u\2\2\u00e3\30\3\2\2\2\u00e4\u00e5\7q\2\2\u00e5\u00e6"+
		"\7t\2\2\u00e6\32\3\2\2\2\u00e7\u00e8\7c\2\2\u00e8\u00e9\7p\2\2\u00e9\u00ea"+
		"\7f\2\2\u00ea\34\3\2\2\2\u00eb\u00ec\7p\2\2\u00ec\u00ed\7q\2\2\u00ed\u00ee"+
		"\7v\2\2\u00ee\36\3\2\2\2\u00ef\u00f0\7?\2\2\u00f0 \3\2\2\2\u00f1\u00f2"+
		"\7\61\2\2\u00f2\u00f3\7?\2\2\u00f3\"\3\2\2\2\u00f4\u00f5\7>\2\2\u00f5"+
		"$\3\2\2\2\u00f6\u00f7\7>\2\2\u00f7\u00f8\7?\2\2\u00f8&\3\2\2\2\u00f9\u00fa"+
		"\7@\2\2\u00fa(\3\2\2\2\u00fb\u00fc\7@\2\2\u00fc\u00fd\7?\2\2\u00fd*\3"+
		"\2\2\2\u00fe\u00ff\7-\2\2\u00ff,\3\2\2\2\u0100\u0101\7/\2\2\u0101.\3\2"+
		"\2\2\u0102\u0103\7,\2\2\u0103\60\3\2\2\2\u0104\u0105\7\61\2\2\u0105\62"+
		"\3\2\2\2\u0106\u0107\7o\2\2\u0107\u0108\7q\2\2\u0108\u0109\7f\2\2\u0109"+
		"\64\3\2\2\2\u010a\u010b\7t\2\2\u010b\u010c\7g\2\2\u010c\u010d\7o\2\2\u010d"+
		"\66\3\2\2\2\u010e\u010f\7\'\2\2\u010f8\3\2\2\2\u0110\u0111\7d\2\2\u0111"+
		"\u0112\7x\2\2\u0112\u0113\7c\2\2\u0113\u0114\7f\2\2\u0114\u0115\7f\2\2"+
		"\u0115:\3\2\2\2\u0116\u0117\7d\2\2\u0117\u0118\7x\2\2\u0118\u0119\7u\2"+
		"\2\u0119\u011a\7w\2\2\u011a\u011b\7d\2\2\u011b<\3\2\2\2\u011c\u011d\7"+
		"d\2\2\u011d\u011e\7x\2\2\u011e\u011f\7r\2\2\u011f\u0120\7q\2\2\u0120\u0121"+
		"\7u\2\2\u0121>\3\2\2\2\u0122\u0123\7d\2\2\u0123\u0124\7x\2\2\u0124\u0125"+
		"\7p\2\2\u0125\u0126\7g\2\2\u0126\u0127\7i\2\2\u0127@\3\2\2\2\u0128\u0129"+
		"\7d\2\2\u0129\u012a\7x\2\2\u012a\u012b\7o\2\2\u012b\u012c\7w\2\2\u012c"+
		"\u012d\7n\2\2\u012dB\3\2\2\2\u012e\u012f\7d\2\2\u012f\u0130\7x\2\2\u0130"+
		"\u0131\7w\2\2\u0131\u0132\7f\2\2\u0132\u0133\7k\2\2\u0133\u0134\7x\2\2"+
		"\u0134D\3\2\2\2\u0135\u0136\7d\2\2\u0136\u0137\7x\2\2\u0137\u0138\7u\2"+
		"\2\u0138\u0139\7f\2\2\u0139\u013a\7k\2\2\u013a\u013b\7x\2\2\u013bF\3\2"+
		"\2\2\u013c\u013d\7d\2\2\u013d\u013e\7x\2\2\u013e\u013f\7u\2\2\u013f\u0140"+
		"\7o\2\2\u0140\u0141\7q\2\2\u0141\u0142\7f\2\2\u0142H\3\2\2\2\u0143\u0144"+
		"\7d\2\2\u0144\u0145\7x\2\2\u0145\u0146\7w\2\2\u0146\u0147\7t\2\2\u0147"+
		"\u0148\7g\2\2\u0148\u0149\7o\2\2\u0149J\3\2\2\2\u014a\u014b\7d\2\2\u014b"+
		"\u014c\7x\2\2\u014c\u014d\7u\2\2\u014d\u014e\7t\2\2\u014e\u014f\7g\2\2"+
		"\u014f\u0150\7o\2\2\u0150L\3\2\2\2\u0151\u0152\7d\2\2\u0152\u0153\7x\2"+
		"\2\u0153\u0154\7q\2\2\u0154\u0155\7t\2\2\u0155N\3\2\2\2\u0156\u0157\7"+
		"d\2\2\u0157\u0158\7x\2\2\u0158\u0159\7c\2\2\u0159\u015a\7p\2\2\u015a\u015b"+
		"\7f\2\2\u015bP\3\2\2\2\u015c\u015d\7d\2\2\u015d\u015e\7x\2\2\u015e\u015f"+
		"\7z\2\2\u015f\u0160\7q\2\2\u0160\u0161\7t\2\2\u0161R\3\2\2\2\u0162\u0163"+
		"\7d\2\2\u0163\u0164\7x\2\2\u0164\u0165\7p\2\2\u0165\u0166\7q\2\2\u0166"+
		"\u0167\7v\2\2\u0167T\3\2\2\2\u0168\u0169\7d\2\2\u0169\u016a\7x\2\2\u016a"+
		"\u016b\7u\2\2\u016b\u016c\7j\2\2\u016c\u016d\7n\2\2\u016dV\3\2\2\2\u016e"+
		"\u016f\7d\2\2\u016f\u0170\7x\2\2\u0170\u0171\7c\2\2\u0171\u0172\7u\2\2"+
		"\u0172\u0173\7j\2\2\u0173\u0174\7t\2\2\u0174X\3\2\2\2\u0175\u0176\7d\2"+
		"\2\u0176\u0177\7x\2\2\u0177\u0178\7n\2\2\u0178\u0179\7u\2\2\u0179\u017a"+
		"\7j\2\2\u017a\u017b\7t\2\2\u017bZ\3\2\2\2\u017c\u017d\7d\2\2\u017d\u017e"+
		"\7x\2\2\u017e\u017f\7t\2\2\u017f\u0180\7q\2\2\u0180\u0181\7n\2\2\u0181"+
		"\\\3\2\2\2\u0182\u0183\7d\2\2\u0183\u0184\7x\2\2\u0184\u0185\7t\2\2\u0185"+
		"\u0186\7q\2\2\u0186\u0187\7t\2\2\u0187^\3\2\2\2\u0188\u0189\7d\2\2\u0189"+
		"\u018a\7x\2\2\u018a\u018b\7w\2\2\u018b\u018c\7n\2\2\u018c\u018d\7v\2\2"+
		"\u018d`\3\2\2\2\u018e\u018f\7d\2\2\u018f\u0190\7x\2\2\u0190\u0191\7w\2"+
		"\2\u0191\u0192\7n\2\2\u0192\u0193\7g\2\2\u0193b\3\2\2\2\u0194\u0195\7"+
		"d\2\2\u0195\u0196\7x\2\2\u0196\u0197\7w\2\2\u0197\u0198\7i\2\2\u0198\u0199"+
		"\7v\2\2\u0199d\3\2\2\2\u019a\u019b\7d\2\2\u019b\u019c\7x\2\2\u019c\u019d"+
		"\7w\2\2\u019d\u019e\7i\2\2\u019e\u019f\7g\2\2\u019ff\3\2\2\2\u01a0\u01a1"+
		"\7d\2\2\u01a1\u01a2\7x\2\2\u01a2\u01a3\7u\2\2\u01a3\u01a4\7n\2\2\u01a4"+
		"\u01a5\7v\2\2\u01a5h\3\2\2\2\u01a6\u01a7\7d\2\2\u01a7\u01a8\7x\2\2\u01a8"+
		"\u01a9\7u\2\2\u01a9\u01aa\7n\2\2\u01aa\u01ab\7g\2\2\u01abj\3\2\2\2\u01ac"+
		"\u01ad\7d\2\2\u01ad\u01ae\7x\2\2\u01ae\u01af\7u\2\2\u01af\u01b0\7i\2\2"+
		"\u01b0\u01b1\7v\2\2\u01b1l\3\2\2\2\u01b2\u01b3\7d\2\2\u01b3\u01b4\7x\2"+
		"\2\u01b4\u01b5\7u\2\2\u01b5\u01b6\7i\2\2\u01b6\u01b7\7g\2\2\u01b7n\3\2"+
		"\2\2\u01b8\u01b9\5+\26\2\u01b9\u01ba\5+\26\2\u01bap\3\2\2\2\u01bb\u01bc"+
		"\7d\2\2\u01bc\u01bd\7x\2\2\u01bd\u01be\7a\2\2\u01be\u01bf\7|\2\2\u01bf"+
		"\u01c0\7g\2\2\u01c0\u01c1\7t\2\2\u01c1\u01c2\7q\2\2\u01c2\u01c3\7a\2\2"+
		"\u01c3\u01c4\7g\2\2\u01c4\u01c5\7z\2\2\u01c5\u01c6\7v\2\2\u01c6\u01c7"+
		"\7g\2\2\u01c7\u01c8\7p\2\2\u01c8\u01c9\7f\2\2\u01c9r\3\2\2\2\u01ca\u01cb"+
		"\7d\2\2\u01cb\u01cc\7x\2\2\u01cc\u01cd\7a\2\2\u01cd\u01ce\7u\2\2\u01ce"+
		"\u01cf\7k\2\2\u01cf\u01d0\7i\2\2\u01d0\u01d1\7p\2\2\u01d1\u01d2\7a\2\2"+
		"\u01d2\u01d3\7g\2\2\u01d3\u01d4\7z\2\2\u01d4\u01d5\7v\2\2\u01d5\u01d6"+
		"\7g\2\2\u01d6\u01d7\7p\2\2\u01d7\u01d8\7f\2\2\u01d8t\3\2\2\2\u01d9\u01da"+
		"\7v\2\2\u01da\u01db\7t\2\2\u01db\u01dc\7w\2\2\u01dc\u01dd\7g\2\2\u01dd"+
		"v\3\2\2\2\u01de\u01df\7h\2\2\u01df\u01e0\7c\2\2\u01e0\u01e1\7n\2\2\u01e1"+
		"\u01e2\7u\2\2\u01e2\u01e3\7g\2\2\u01e3x\3\2\2\2\u01e4\u01e5\7<\2\2\u01e5"+
		"\u01e6\7?\2\2\u01e6z\3\2\2\2\u01e7\u01e8\7j\2\2\u01e8\u01e9\7c\2\2\u01e9"+
		"\u01ea\7x\2\2\u01ea\u01eb\7q\2\2\u01eb\u01ec\7e\2\2\u01ec|\3\2\2\2\u01ed"+
		"\u01ee\7c\2\2\u01ee\u01ef\7u\2\2\u01ef\u01f0\7u\2\2\u01f0\u01f1\7w\2\2"+
		"\u01f1\u01f2\7o\2\2\u01f2\u01f3\7g\2\2\u01f3~\3\2\2\2\u01f4\u01f5\5\u0083"+
		"B\2\u01f5\u01f6\7)\2\2\u01f6\u01f7\7d\2\2\u01f7\u01f9\3\2\2\2\u01f8\u01fa"+
		"\t\2\2\2\u01f9\u01f8\3\2\2\2\u01fa\u01fb\3\2\2\2\u01fb\u01f9\3\2\2\2\u01fb"+
		"\u01fc\3\2\2\2\u01fc\u0211\3\2\2\2\u01fd\u01fe\5\u0083B\2\u01fe\u01ff"+
		"\7)\2\2\u01ff\u0200\7f\2\2\u0200\u0203\3\2\2\2\u0201\u0204\5+\26\2\u0202"+
		"\u0204\5-\27\2\u0203\u0201\3\2\2\2\u0203\u0202\3\2\2\2\u0203\u0204\3\2"+
		"\2\2\u0204\u0205\3\2\2\2\u0205\u0206\5\u0081A\2\u0206\u0211\3\2\2\2\u0207"+
		"\u0208\5\u0083B\2\u0208\u0209\7)\2\2\u0209\u020a\7z\2\2\u020a\u020c\3"+
		"\2\2\2\u020b\u020d\t\3\2\2\u020c\u020b\3\2\2\2\u020d\u020e\3\2\2\2\u020e"+
		"\u020c\3\2\2\2\u020e\u020f\3\2\2\2\u020f\u0211\3\2\2\2\u0210\u01f4\3\2"+
		"\2\2\u0210\u01fd\3\2\2\2\u0210\u0207\3\2\2\2\u0211\u0080\3\2\2\2\u0212"+
		"\u0213\5\u0083B\2\u0213\u0082\3\2\2\2\u0214\u0216\5\u008dG\2\u0215\u0214"+
		"\3\2\2\2\u0216\u0217\3\2\2\2\u0217\u0215\3\2\2\2\u0217\u0218\3\2\2\2\u0218"+
		"\u0084\3\2\2\2\u0219\u021c\5+\26\2\u021a\u021c\5-\27\2\u021b\u0219\3\2"+
		"\2\2\u021b\u021a\3\2\2\2\u021c\u0086\3\2\2\2\u021d\u021e\7\60\2\2\u021e"+
		"\u0088\3\2\2\2\u021f\u0222\5\u008fH\2\u0220\u0222\5\u008bF\2\u0221\u021f"+
		"\3\2\2\2\u0221\u0220\3\2\2\2\u0222\u0228\3\2\2\2\u0223\u0227\5\u008fH"+
		"\2\u0224\u0227\5\u008bF\2\u0225\u0227\5\u008dG\2\u0226\u0223\3\2\2\2\u0226"+
		"\u0224\3\2\2\2\u0226\u0225\3\2\2\2\u0227\u022a\3\2\2\2\u0228\u0226\3\2"+
		"\2\2\u0228\u0229\3\2\2\2\u0229\u008a\3\2\2\2\u022a\u0228\3\2\2\2\u022b"+
		"\u022c\7a\2\2\u022c\u008c\3\2\2\2\u022d\u022e\t\4\2\2\u022e\u008e\3\2"+
		"\2\2\u022f\u0230\t\5\2\2\u0230\u0090\3\2\2\2\u0231\u0232\7*\2\2\u0232"+
		"\u0092\3\2\2\2\u0233\u0234\7+\2\2\u0234\u0094\3\2\2\2\u0235\u0236\7]\2"+
		"\2\u0236\u0096\3\2\2\2\u0237\u0238\7_\2\2\u0238\u0098\3\2\2\2\u0239\u023a"+
		"\7}\2\2\u023a\u009a\3\2\2\2\u023b\u023c\7\177\2\2\u023c\u009c\3\2\2\2"+
		"\u023d\u023e\7.\2\2\u023e\u009e\3\2\2\2\u023f\u0240\7<\2\2\u0240\u00a0"+
		"\3\2\2\2\u0241\u0242\7=\2\2\u0242\u00a2\3\2\2\2\u0243\u0244\7)\2\2\u0244"+
		"\u00a4\3\2\2\2\u0245\u0246\7>\2\2\u0246\u0247\7/\2\2\u0247\u00a6\3\2\2"+
		"\2\u0248\u0249\7/\2\2\u0249\u024a\7@\2\2\u024a\u00a8\3\2\2\2\u024b\u024d"+
		"\t\6\2\2\u024c\u024b\3\2\2\2\u024d\u024e\3\2\2\2\u024e\u024c\3\2\2\2\u024e"+
		"\u024f\3\2\2\2\u024f\u0250\3\2\2\2\u0250\u0251\bU\2\2\u0251\u00aa\3\2"+
		"\2\2\u0252\u0253\7\61\2\2\u0253\u0254\7,\2\2\u0254\u0258\3\2\2\2\u0255"+
		"\u0257\13\2\2\2\u0256\u0255\3\2\2\2\u0257\u025a\3\2\2\2\u0258\u0259\3"+
		"\2\2\2\u0258\u0256\3\2\2\2\u0259\u025b\3\2\2\2\u025a\u0258\3\2\2\2\u025b"+
		"\u025c\7,\2\2\u025c\u025d\7\61\2\2\u025d\u025e\3\2\2\2\u025e\u025f\bV"+
		"\2\2\u025f\u00ac\3\2\2\2\u0260\u0261\7\61\2\2\u0261\u0262\7\61\2\2\u0262"+
		"\u0266\3\2\2\2\u0263\u0265\n\7\2\2\u0264\u0263\3\2\2\2\u0265\u0268\3\2"+
		"\2\2\u0266\u0264\3\2\2\2\u0266\u0267\3\2\2\2\u0267\u0269\3\2\2\2\u0268"+
		"\u0266\3\2\2\2\u0269\u026a\bW\2\2\u026a\u00ae\3\2\2\2\17\2\u01fb\u0203"+
		"\u020e\u0210\u0217\u021b\u0221\u0226\u0228\u024e\u0258\u0266\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}