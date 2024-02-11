// Generated from /home/levente/Documents/University/theta-fresh/subprojects/common/grammar/src/main/antlr/Declarations.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class DeclarationsParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.10.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		BOOLTYPE=1, INTTYPE=2, RATTYPE=3, BVTYPE=4, FPTYPE=5, FUNC=6, ARRAY=7, 
		IF=8, THEN=9, ELSE=10, IFF=11, ITE=12, IMPLY=13, FORALL=14, EXISTS=15, 
		OR=16, AND=17, XOR=18, NOT=19, EQ=20, NEQ=21, LT=22, LEQ=23, GT=24, GEQ=25, 
		PLUS=26, MINUS=27, MUL=28, DIV=29, MOD=30, REM=31, PERCENT=32, BV_CONCAT=33, 
		BV_ZERO_EXTEND=34, BV_SIGN_EXTEND=35, BV_ADD=36, BV_SUB=37, BV_POS=38, 
		BV_NEG=39, BV_MUL=40, BV_UDIV=41, BV_SDIV=42, BV_SMOD=43, BV_UREM=44, 
		BV_SREM=45, BV_OR=46, BV_AND=47, BV_XOR=48, BV_NOT=49, BV_SHL=50, BV_ASHR=51, 
		BV_LSHR=52, BV_ROL=53, BV_ROR=54, BV_ULT=55, BV_ULE=56, BV_UGT=57, BV_UGE=58, 
		BV_SLT=59, BV_SLE=60, BV_SGT=61, BV_SGE=62, FP_ABS=63, FP_FROM_BV=64, 
		FP_IS_NAN=65, FPMAX=66, FPMIN=67, FPREM=68, FPROUNDTOINT=69, FPSQRT=70, 
		FPTOBV=71, FPTOFP=72, FPSUB=73, FPADD=74, FPMUL=75, FPDIV=76, FPPOS=77, 
		FPNEG=78, TRUE=79, READ=80, WRITE=81, PRIME=82, EXTRACT=83, BV_TYPE_DECL=84, 
		FP_TYPE_DECL=85, FP_ROUNDINGMODE=86, FALSE=87, DEFAULT=88, ASSIGN=89, 
		HAVOC=90, ASSUME=91, RETURN=92, BV=93, INT=94, NAT=95, SIGN=96, DOT=97, 
		ID=98, UNDERSCORE=99, DIGIT=100, LETTER=101, LPAREN=102, RPAREN=103, LBRACK=104, 
		RBRACK=105, LBRAC=106, RBRAC=107, COMMA=108, COLON=109, SEMICOLON=110, 
		QUOT=111, LARROW=112, RARROW=113, WS=114, COMMENT=115, LINE_COMMENT=116;
	public static final int
		RULE_decl = 0, RULE_declList = 1, RULE_type = 2, RULE_typeList = 3, RULE_boolType = 4, 
		RULE_intType = 5, RULE_ratType = 6, RULE_funcType = 7, RULE_arrayType = 8, 
		RULE_bvType = 9, RULE_fpType = 10;
	private static String[] makeRuleNames() {
		return new String[] {
			"decl", "declList", "type", "typeList", "boolType", "intType", "ratType", 
			"funcType", "arrayType", "bvType", "fpType"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, "'if'", "'then'", "'else'", 
			"'iff'", "'ite'", "'=>'", "'forall'", "'exists'", "'or'", "'and'", "'xor'", 
			"'not'", "'='", "'/='", "'<'", "'<='", "'>'", "'>='", "'+'", "'-'", "'*'", 
			"'div'", "'mod'", "'rem'", "'%'", null, "'bv_zero_extend'", "'bv_sign_extend'", 
			"'bvadd'", "'bvsub'", "'bvpos'", "'bvneg'", "'bvmul'", "'bvudiv'", "'bvsdiv'", 
			"'bvsmod'", "'bvurem'", "'bvsrem'", "'bvor'", "'bvand'", "'bvxor'", "'bvnot'", 
			"'bvshl'", "'bvashr'", "'bvlshr'", "'bvrol'", "'bvror'", "'bvult'", "'bvule'", 
			"'bvugt'", "'bvuge'", "'bvslt'", "'bvsle'", "'bvsgt'", "'bvsge'", "'fpabs'", 
			null, "'fpisnan'", "'fpmax'", "'fpmin'", "'fprem'", null, null, null, 
			null, "'fpsub'", null, "'fpmul'", null, "'fppos'", "'fpneg'", "'true'", 
			"'read'", "'write'", "'prime'", "'extract'", null, null, null, "'false'", 
			"'default'", "'assign'", "'havoc'", "'assume'", "'return'", null, null, 
			null, null, "'.'", null, "'_'", null, null, "'('", "')'", "'['", "']'", 
			"'{'", "'}'", "','", "':'", "';'", "'''", "'<-'", "'->'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "BOOLTYPE", "INTTYPE", "RATTYPE", "BVTYPE", "FPTYPE", "FUNC", "ARRAY", 
			"IF", "THEN", "ELSE", "IFF", "ITE", "IMPLY", "FORALL", "EXISTS", "OR", 
			"AND", "XOR", "NOT", "EQ", "NEQ", "LT", "LEQ", "GT", "GEQ", "PLUS", "MINUS", 
			"MUL", "DIV", "MOD", "REM", "PERCENT", "BV_CONCAT", "BV_ZERO_EXTEND", 
			"BV_SIGN_EXTEND", "BV_ADD", "BV_SUB", "BV_POS", "BV_NEG", "BV_MUL", "BV_UDIV", 
			"BV_SDIV", "BV_SMOD", "BV_UREM", "BV_SREM", "BV_OR", "BV_AND", "BV_XOR", 
			"BV_NOT", "BV_SHL", "BV_ASHR", "BV_LSHR", "BV_ROL", "BV_ROR", "BV_ULT", 
			"BV_ULE", "BV_UGT", "BV_UGE", "BV_SLT", "BV_SLE", "BV_SGT", "BV_SGE", 
			"FP_ABS", "FP_FROM_BV", "FP_IS_NAN", "FPMAX", "FPMIN", "FPREM", "FPROUNDTOINT", 
			"FPSQRT", "FPTOBV", "FPTOFP", "FPSUB", "FPADD", "FPMUL", "FPDIV", "FPPOS", 
			"FPNEG", "TRUE", "READ", "WRITE", "PRIME", "EXTRACT", "BV_TYPE_DECL", 
			"FP_TYPE_DECL", "FP_ROUNDINGMODE", "FALSE", "DEFAULT", "ASSIGN", "HAVOC", 
			"ASSUME", "RETURN", "BV", "INT", "NAT", "SIGN", "DOT", "ID", "UNDERSCORE", 
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

	@Override
	public String getGrammarFileName() { return "Declarations.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public DeclarationsParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class DeclContext extends ParserRuleContext {
		public Token name;
		public TypeContext ttype;
		public TerminalNode LPAREN() { return getToken(DeclarationsParser.LPAREN, 0); }
		public TerminalNode RPAREN() { return getToken(DeclarationsParser.RPAREN, 0); }
		public TerminalNode ID() { return getToken(DeclarationsParser.ID, 0); }
		public TypeContext type() {
			return getRuleContext(TypeContext.class,0);
		}
		public DeclContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_decl; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterDecl(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitDecl(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitDecl(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DeclContext decl() throws RecognitionException {
		DeclContext _localctx = new DeclContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_decl);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(22);
			match(LPAREN);
			setState(23);
			((DeclContext)_localctx).name = match(ID);
			setState(24);
			((DeclContext)_localctx).ttype = type();
			setState(25);
			match(RPAREN);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DeclListContext extends ParserRuleContext {
		public DeclContext decl;
		public List<DeclContext> decls = new ArrayList<DeclContext>();
		public List<DeclContext> decl() {
			return getRuleContexts(DeclContext.class);
		}
		public DeclContext decl(int i) {
			return getRuleContext(DeclContext.class,i);
		}
		public List<TerminalNode> COMMA() { return getTokens(DeclarationsParser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(DeclarationsParser.COMMA, i);
		}
		public DeclListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_declList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterDeclList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitDeclList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitDeclList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DeclListContext declList() throws RecognitionException {
		DeclListContext _localctx = new DeclListContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_declList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(27);
			((DeclListContext)_localctx).decl = decl();
			((DeclListContext)_localctx).decls.add(((DeclListContext)_localctx).decl);
			}
			setState(32);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==COMMA) {
				{
				{
				setState(28);
				match(COMMA);
				setState(29);
				((DeclListContext)_localctx).decl = decl();
				((DeclListContext)_localctx).decls.add(((DeclListContext)_localctx).decl);
				}
				}
				setState(34);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypeContext extends ParserRuleContext {
		public BoolTypeContext boolType() {
			return getRuleContext(BoolTypeContext.class,0);
		}
		public IntTypeContext intType() {
			return getRuleContext(IntTypeContext.class,0);
		}
		public RatTypeContext ratType() {
			return getRuleContext(RatTypeContext.class,0);
		}
		public FuncTypeContext funcType() {
			return getRuleContext(FuncTypeContext.class,0);
		}
		public ArrayTypeContext arrayType() {
			return getRuleContext(ArrayTypeContext.class,0);
		}
		public BvTypeContext bvType() {
			return getRuleContext(BvTypeContext.class,0);
		}
		public FpTypeContext fpType() {
			return getRuleContext(FpTypeContext.class,0);
		}
		public TypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_type; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeContext type() throws RecognitionException {
		TypeContext _localctx = new TypeContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_type);
		try {
			setState(42);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(35);
				boolType();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(36);
				intType();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(37);
				ratType();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(38);
				funcType();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(39);
				arrayType();
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(40);
				bvType();
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(41);
				fpType();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypeListContext extends ParserRuleContext {
		public TypeContext type;
		public List<TypeContext> types = new ArrayList<TypeContext>();
		public List<TypeContext> type() {
			return getRuleContexts(TypeContext.class);
		}
		public TypeContext type(int i) {
			return getRuleContext(TypeContext.class,i);
		}
		public List<TerminalNode> COMMA() { return getTokens(DeclarationsParser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(DeclarationsParser.COMMA, i);
		}
		public TypeListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterTypeList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitTypeList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitTypeList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeListContext typeList() throws RecognitionException {
		TypeListContext _localctx = new TypeListContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_typeList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(44);
			((TypeListContext)_localctx).type = type();
			((TypeListContext)_localctx).types.add(((TypeListContext)_localctx).type);
			}
			setState(49);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==COMMA) {
				{
				{
				setState(45);
				match(COMMA);
				setState(46);
				((TypeListContext)_localctx).type = type();
				((TypeListContext)_localctx).types.add(((TypeListContext)_localctx).type);
				}
				}
				setState(51);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BoolTypeContext extends ParserRuleContext {
		public TerminalNode BOOLTYPE() { return getToken(DeclarationsParser.BOOLTYPE, 0); }
		public BoolTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_boolType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterBoolType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitBoolType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitBoolType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BoolTypeContext boolType() throws RecognitionException {
		BoolTypeContext _localctx = new BoolTypeContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_boolType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(52);
			match(BOOLTYPE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IntTypeContext extends ParserRuleContext {
		public TerminalNode INTTYPE() { return getToken(DeclarationsParser.INTTYPE, 0); }
		public IntTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_intType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterIntType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitIntType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitIntType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IntTypeContext intType() throws RecognitionException {
		IntTypeContext _localctx = new IntTypeContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_intType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(54);
			match(INTTYPE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class RatTypeContext extends ParserRuleContext {
		public TerminalNode RATTYPE() { return getToken(DeclarationsParser.RATTYPE, 0); }
		public RatTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ratType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterRatType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitRatType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitRatType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final RatTypeContext ratType() throws RecognitionException {
		RatTypeContext _localctx = new RatTypeContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_ratType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(56);
			match(RATTYPE);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FuncTypeContext extends ParserRuleContext {
		public TypeContext from;
		public TypeContext to;
		public TerminalNode LPAREN() { return getToken(DeclarationsParser.LPAREN, 0); }
		public TerminalNode FUNC() { return getToken(DeclarationsParser.FUNC, 0); }
		public TerminalNode RPAREN() { return getToken(DeclarationsParser.RPAREN, 0); }
		public List<TypeContext> type() {
			return getRuleContexts(TypeContext.class);
		}
		public TypeContext type(int i) {
			return getRuleContext(TypeContext.class,i);
		}
		public FuncTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_funcType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterFuncType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitFuncType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitFuncType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FuncTypeContext funcType() throws RecognitionException {
		FuncTypeContext _localctx = new FuncTypeContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_funcType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(58);
			match(LPAREN);
			setState(59);
			match(FUNC);
			setState(60);
			((FuncTypeContext)_localctx).from = type();
			setState(61);
			((FuncTypeContext)_localctx).to = type();
			setState(62);
			match(RPAREN);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ArrayTypeContext extends ParserRuleContext {
		public TypeContext indexType;
		public TypeContext elemType;
		public List<TerminalNode> LPAREN() { return getTokens(DeclarationsParser.LPAREN); }
		public TerminalNode LPAREN(int i) {
			return getToken(DeclarationsParser.LPAREN, i);
		}
		public TerminalNode ARRAY() { return getToken(DeclarationsParser.ARRAY, 0); }
		public TerminalNode LBRACK() { return getToken(DeclarationsParser.LBRACK, 0); }
		public TerminalNode RBRACK() { return getToken(DeclarationsParser.RBRACK, 0); }
		public TerminalNode RARROW() { return getToken(DeclarationsParser.RARROW, 0); }
		public List<TerminalNode> RPAREN() { return getTokens(DeclarationsParser.RPAREN); }
		public TerminalNode RPAREN(int i) {
			return getToken(DeclarationsParser.RPAREN, i);
		}
		public List<TypeContext> type() {
			return getRuleContexts(TypeContext.class);
		}
		public TypeContext type(int i) {
			return getRuleContext(TypeContext.class,i);
		}
		public ArrayTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_arrayType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterArrayType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitArrayType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitArrayType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ArrayTypeContext arrayType() throws RecognitionException {
		ArrayTypeContext _localctx = new ArrayTypeContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_arrayType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(64);
			match(LPAREN);
			setState(65);
			match(ARRAY);
			setState(66);
			match(LPAREN);
			setState(67);
			match(LBRACK);
			setState(68);
			((ArrayTypeContext)_localctx).indexType = type();
			setState(69);
			match(RBRACK);
			setState(70);
			match(RARROW);
			setState(71);
			((ArrayTypeContext)_localctx).elemType = type();
			setState(72);
			match(RPAREN);
			setState(73);
			match(RPAREN);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BvTypeContext extends ParserRuleContext {
		public Token size;
		public TerminalNode LPAREN() { return getToken(DeclarationsParser.LPAREN, 0); }
		public TerminalNode BVTYPE() { return getToken(DeclarationsParser.BVTYPE, 0); }
		public TerminalNode RPAREN() { return getToken(DeclarationsParser.RPAREN, 0); }
		public TerminalNode INT() { return getToken(DeclarationsParser.INT, 0); }
		public BvTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bvType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterBvType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitBvType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitBvType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BvTypeContext bvType() throws RecognitionException {
		BvTypeContext _localctx = new BvTypeContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_bvType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(75);
			match(LPAREN);
			setState(76);
			match(BVTYPE);
			setState(77);
			((BvTypeContext)_localctx).size = match(INT);
			setState(78);
			match(RPAREN);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FpTypeContext extends ParserRuleContext {
		public Token exponent;
		public Token significand;
		public TerminalNode LPAREN() { return getToken(DeclarationsParser.LPAREN, 0); }
		public TerminalNode FPTYPE() { return getToken(DeclarationsParser.FPTYPE, 0); }
		public TerminalNode RPAREN() { return getToken(DeclarationsParser.RPAREN, 0); }
		public List<TerminalNode> INT() { return getTokens(DeclarationsParser.INT); }
		public TerminalNode INT(int i) {
			return getToken(DeclarationsParser.INT, i);
		}
		public FpTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_fpType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).enterFpType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof DeclarationsListener ) ((DeclarationsListener)listener).exitFpType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof DeclarationsVisitor ) return ((DeclarationsVisitor<? extends T>)visitor).visitFpType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FpTypeContext fpType() throws RecognitionException {
		FpTypeContext _localctx = new FpTypeContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_fpType);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(80);
			match(LPAREN);
			setState(81);
			match(FPTYPE);
			setState(82);
			((FpTypeContext)_localctx).exponent = match(INT);
			setState(83);
			((FpTypeContext)_localctx).significand = match(INT);
			setState(84);
			match(RPAREN);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\u0004\u0001tW\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002\u0002"+
		"\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002\u0005"+
		"\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002\b\u0007"+
		"\b\u0002\t\u0007\t\u0002\n\u0007\n\u0001\u0000\u0001\u0000\u0001\u0000"+
		"\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0005\u0001"+
		"\u001f\b\u0001\n\u0001\f\u0001\"\t\u0001\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0003\u0002+\b"+
		"\u0002\u0001\u0003\u0001\u0003\u0001\u0003\u0005\u00030\b\u0003\n\u0003"+
		"\f\u00033\t\u0003\u0001\u0004\u0001\u0004\u0001\u0005\u0001\u0005\u0001"+
		"\u0006\u0001\u0006\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001"+
		"\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\t\u0001\t\u0001\t\u0001\t\u0001"+
		"\t\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0000\u0000"+
		"\u000b\u0000\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014\u0000\u0000"+
		"S\u0000\u0016\u0001\u0000\u0000\u0000\u0002\u001b\u0001\u0000\u0000\u0000"+
		"\u0004*\u0001\u0000\u0000\u0000\u0006,\u0001\u0000\u0000\u0000\b4\u0001"+
		"\u0000\u0000\u0000\n6\u0001\u0000\u0000\u0000\f8\u0001\u0000\u0000\u0000"+
		"\u000e:\u0001\u0000\u0000\u0000\u0010@\u0001\u0000\u0000\u0000\u0012K"+
		"\u0001\u0000\u0000\u0000\u0014P\u0001\u0000\u0000\u0000\u0016\u0017\u0005"+
		"f\u0000\u0000\u0017\u0018\u0005b\u0000\u0000\u0018\u0019\u0003\u0004\u0002"+
		"\u0000\u0019\u001a\u0005g\u0000\u0000\u001a\u0001\u0001\u0000\u0000\u0000"+
		"\u001b \u0003\u0000\u0000\u0000\u001c\u001d\u0005l\u0000\u0000\u001d\u001f"+
		"\u0003\u0000\u0000\u0000\u001e\u001c\u0001\u0000\u0000\u0000\u001f\"\u0001"+
		"\u0000\u0000\u0000 \u001e\u0001\u0000\u0000\u0000 !\u0001\u0000\u0000"+
		"\u0000!\u0003\u0001\u0000\u0000\u0000\" \u0001\u0000\u0000\u0000#+\u0003"+
		"\b\u0004\u0000$+\u0003\n\u0005\u0000%+\u0003\f\u0006\u0000&+\u0003\u000e"+
		"\u0007\u0000\'+\u0003\u0010\b\u0000(+\u0003\u0012\t\u0000)+\u0003\u0014"+
		"\n\u0000*#\u0001\u0000\u0000\u0000*$\u0001\u0000\u0000\u0000*%\u0001\u0000"+
		"\u0000\u0000*&\u0001\u0000\u0000\u0000*\'\u0001\u0000\u0000\u0000*(\u0001"+
		"\u0000\u0000\u0000*)\u0001\u0000\u0000\u0000+\u0005\u0001\u0000\u0000"+
		"\u0000,1\u0003\u0004\u0002\u0000-.\u0005l\u0000\u0000.0\u0003\u0004\u0002"+
		"\u0000/-\u0001\u0000\u0000\u000003\u0001\u0000\u0000\u00001/\u0001\u0000"+
		"\u0000\u000012\u0001\u0000\u0000\u00002\u0007\u0001\u0000\u0000\u0000"+
		"31\u0001\u0000\u0000\u000045\u0005\u0001\u0000\u00005\t\u0001\u0000\u0000"+
		"\u000067\u0005\u0002\u0000\u00007\u000b\u0001\u0000\u0000\u000089\u0005"+
		"\u0003\u0000\u00009\r\u0001\u0000\u0000\u0000:;\u0005f\u0000\u0000;<\u0005"+
		"\u0006\u0000\u0000<=\u0003\u0004\u0002\u0000=>\u0003\u0004\u0002\u0000"+
		">?\u0005g\u0000\u0000?\u000f\u0001\u0000\u0000\u0000@A\u0005f\u0000\u0000"+
		"AB\u0005\u0007\u0000\u0000BC\u0005f\u0000\u0000CD\u0005h\u0000\u0000D"+
		"E\u0003\u0004\u0002\u0000EF\u0005i\u0000\u0000FG\u0005q\u0000\u0000GH"+
		"\u0003\u0004\u0002\u0000HI\u0005g\u0000\u0000IJ\u0005g\u0000\u0000J\u0011"+
		"\u0001\u0000\u0000\u0000KL\u0005f\u0000\u0000LM\u0005\u0004\u0000\u0000"+
		"MN\u0005^\u0000\u0000NO\u0005g\u0000\u0000O\u0013\u0001\u0000\u0000\u0000"+
		"PQ\u0005f\u0000\u0000QR\u0005\u0005\u0000\u0000RS\u0005^\u0000\u0000S"+
		"T\u0005^\u0000\u0000TU\u0005g\u0000\u0000U\u0015\u0001\u0000\u0000\u0000"+
		"\u0003 *1";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}