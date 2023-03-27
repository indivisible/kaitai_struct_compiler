package io.kaitai.struct.languages

import io.kaitai.struct.{ClassTypeProvider, RuntimeConfig, Utils}
import io.kaitai.struct.datatype.{DataType, FixedEndian, InheritedEndian, KSError, ValidationNotEqualError, NeedRaw, LittleEndian, BigEndian}
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.format._
import io.kaitai.struct.languages.components._
import io.kaitai.struct.translators.LuaTranslator

class WiresharkLuaCompiler(typeProvider: ClassTypeProvider, config: RuntimeConfig)
  extends LuaCompiler(typeProvider, config) {

  import WiresharkLuaCompiler._

  def protoName: String = "proto"

  override def fileHeader(topClassName: String): Unit = {
    outHeader.puts(s"-- $headerComment")
    outHeader.puts("--")
    outHeader.puts("-- This file is compatible with Lua 5.3")
    outHeader.puts

    importList.add("package.prepend_path(\"plugins/kaitai_struct_lua_runtime\")")
    importList.add("local class = require(\"class\")")
    importList.add("require(\"tvbstream\")")
    importList.add("require(\"kaitaistruct\")")

    val className = type2class(topClassName)
    importList.add(s"local $protoName = Proto('$topClassName', '$className')")
    importList.add(s"$protoName.fields = {}")
    out.puts
    out.puts(s"function ${protoName}.dissector(tvb, pinfo, root)")
    out.inc
    out.puts(s"pinfo.cols.protocol = '$className'")
    out.puts(s"local tree = root:add($protoName, tvb(), '$className')")
    out.puts(s"local io = $kstreamName(TVBStream(tvb))")
    out.puts(s"local obj = $className(io, tree)")
    out.dec
    out.puts("end")
    out.puts("")
  }

  override def fileFooter(topClassName: String): Unit = {
    //out.puts("local udp_port = DissectorTable.get(\"udp.port\")")
    //out.puts(f"udp_port:add(11159, $protoName)")
  }

  override def classConstructorHeader(name: List[String], parentType: DataType, rootClassName: List[String], isHybrid: Boolean, params: List[ParamDefSpec]): Unit = {
    val endianAdd = if (isHybrid) ", is_le" else ""
    val paramsList = Utils.join(params.map((p) => paramName(p.id)), "", ", ", ", ")

    out.puts(s"function ${types2class(name)}:_init($paramsList" + s"io, tree, parent, root$endianAdd)")
    out.inc
    out.puts(s"$kstructName._init(self, io)")
    out.puts("self._parent = parent")
    out.puts("self._root = root or self")
    out.puts("self._tree = tree")
    if (isHybrid)
      out.puts("self._is_le = is_le")

    // Store parameters passed to us
    params.foreach((p) => handleAssignmentSimple(p.id, paramName(p.id)))
  }

  def attr2wireshark(attrType: DataType): String =
    attrType match {
      case _:BytesLimitType => "BYTES"
      case Int1Type(false) => "UINT8"
      case Int1Type(true) => "INT8"
      case IntMultiType(true, _, _) => "INT32"
      case IntMultiType(false, _, _) => "UINT32"
      case BitsType1(_) => "UINT8"
      // FIXME: is this how they work?
      case BitsType(_, _) => "BYTES"
      case FloatMultiType(_, _) => "FLOAT"
      case _:StrType => "STRINGZ"
      case _ => "BYTES"
    }


  override def attrUserTypeParse(id: Identifier, dataType: UserType, io: String, rep: RepeatSpec, defEndian: Option[FixedEndian], assignType: DataType): Unit = {
    var tvbCalcSize = true
    var tvb = s"$io._io.tvb(_offset, 0)"
    val newIO = dataType match {
      case knownSizeType: UserTypeFromBytes =>
        // we have a fixed buffer, thus we shall create separate IO for it
        tvb = s"_tvb"
        tvbCalcSize = false
        createSubstream(id, knownSizeType.bytes, io, rep, defEndian)
      case _: UserTypeInstream =>
        // no fixed buffer, just use regular IO
        io
    }
    val expr = parseExpr(dataType, dataType, newIO, defEndian)
    out.puts(s"local _tree = self._tree:add($tvb, '${idToStr(id)}')")
    // FIXME: ignores autoread
    handleAssignment(id, expr, rep, false)
    if (tvbCalcSize) {
      out.puts(s"_tree:set_len($io:pos() - _offset)")
    }
  }

  def protoFieldName(id: Identifier): String = {
    val prefix = typeProvider.nowClass.name.map(x => type2class(x)).mkString("_")
    s"${prefix}_${publicMemberName(id)}"
  }

  override def attrDebugStart(attrId: Identifier, attrType: DataType, io: Option[String], rep: RepeatSpec): Unit = {
    io match {
      case Some(ioStr) => out.puts(s"local _offset = $ioStr:pos()")
    }
  }

  override def attrDebugEnd(attrName: Identifier, attrType: DataType, io: String, repeat: RepeatSpec): Unit = {
    attrType match {
      case _:UserType | _:SwitchType | _:ArrayType => {}
      case _ =>
        val spec = attr2wireshark(attrType)
        val varName = protoFieldName(attrName)
        val shortName = idToStr(attrName)
        val dotName = typeProvider.nowClass.name.map(x => type2class(x)).mkString(".") + "." + publicMemberName(attrName)
        // FIXME: hack
        importList.add(s"local $varName = ProtoField.new('$shortName', '$dotName', ftypes.$spec)")
        importList.add(s"table.insert($protoName.fields, $varName)")
        out.puts(s"self._tree:add($varName, $io._io.tvb(_offset, $io:pos() - _offset), ${privateMemberName(attrName)})")
    }
  }

  override def parseExpr(dataType: DataType, assignType: DataType, io: String, defEndian: Option[FixedEndian]): String = dataType match {
    case t: ReadableType =>
      s"$io:read_${t.apiCall(defEndian)}()"
    case blt: BytesLimitType =>
      s"$io:read_bytes(${expression(blt.size)})"
    case _: BytesEosType =>
      s"$io:read_bytes_full()"
    case BytesTerminatedType(terminator, include, consume, eosError, _) =>
      s"$io:read_bytes_term($terminator, $include, $consume, $eosError)"
    case BitsType1(bitEndian) =>
      s"$io:read_bits_int_${bitEndian.toSuffix}(1) ~= 0"
    case BitsType(width: Int, bitEndian) =>
      s"$io:read_bits_int_${bitEndian.toSuffix}($width)"
    case t: UserType =>
      val addParams = Utils.join(t.args.map((a) => translator.translate(a)), "", ", ", ", ")
      val addArgs = if (t.isOpaque) {
        ""
      } else {
        val parent = t.forcedParent match {
          case Some(USER_TYPE_NO_PARENT) => "nil"
          case Some(fp) => translator.translate(fp)
          case None => "self"
        }
        val addEndian = t.classSpec.get.meta.endian match {
          case Some(InheritedEndian) => ", self._is_le"
          case _ => ""
        }
        s", _tree, $parent, self._root$addEndian"
      }
      s"${types2class(t.classSpec.get.name)}($addParams$io$addArgs)"
  }

  override def allocateIO(varName: Identifier, rep: RepeatSpec): String = {
    val varStr = privateMemberName(varName)

    val args = getRawIdExpr(varName, rep)

    out.puts("local _tvb = self._io._io.tvb(_offset, self._io:pos() - _offset)")
    out.puts(s"local _io = $kstreamName(TVBStream(_tvb))")
    "_io"
  }
}

object WiresharkLuaCompiler extends LanguageCompilerStatic
    with UpperCamelCaseClasses
    with StreamStructNames
    with ExceptionNames {
  override def getCompiler(
    tp: ClassTypeProvider,
    config: RuntimeConfig
  ): LanguageCompiler = new WiresharkLuaCompiler(tp, config)

  def idToStr(id: Identifier): String =
    id match {
      case SpecialIdentifier(name) => name
      case NamedIdentifier(name) => name
      case NumberedIdentifier(idx) => s"_${NumberedIdentifier.TEMPLATE}$idx"
      case InstanceIdentifier(name) => s"_m_$name"
      case RawIdentifier(innerId) => s"_raw_${idToStr(innerId)}"
    }

  def publicMemberName(id: Identifier): String =
    id match {
      case InstanceIdentifier(name) => name
      case _ => idToStr(id)
    }

  override def kstructName: String = "KaitaiStruct"
  override def kstreamName: String = "KaitaiStream"
  override def ksErrorName(err: KSError): String = err.name

  def types2class(name: List[String]): String =
    name.map(x => type2class(x)).mkString(".")
}
