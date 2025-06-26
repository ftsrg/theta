import kotlinx.serialization.*
import kotlinx.serialization.descriptors.*
import kotlinx.serialization.encoding.*
import kotlinx.serialization.json.Json
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.polymorphic
import kotlinx.serialization.modules.subclass

@Polymorphic
interface Type

@Serializable
@SerialName("Bool")
data object BoolType : Type

@Serializable
@SerialName("Int")
data class IntType(val a: Int) : Type

@Serializable
@SerialName("String")
data class StringType(val b: Int) : Type

// Generic ArrayType with custom serializer to avoid circular dependency
@Serializable(with = ArrayTypeSerializer::class)
@SerialName("Array")
data class ArrayType<IndexType : Type, ElemType : Type>(
    val indexType: IndexType,
    val elemType: ElemType,
) : Type

object ArrayTypeSerializer : KSerializer<ArrayType<out Type, out Type>> {
    override val descriptor: SerialDescriptor = buildClassSerialDescriptor("Array") {
        element<String>("indexType")
        element<String>("elemType")
    }

    override fun serialize(encoder: Encoder, value: ArrayType<out Type, out Type>) {
        encoder.encodeStructure(descriptor) {
            // Serialize the actual type objects polymorphically
            encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class), value.indexType)
            encodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class), value.elemType)
        }
    }

    override fun deserialize(decoder: Decoder): ArrayType<Type, Type> {
        return decoder.decodeStructure(descriptor) {
            var indexType: Type? = null
            var elemType: Type? = null

            while (true) {
                when (val index = decodeElementIndex(descriptor)) {
                    0 -> indexType = decodeSerializableElement(descriptor, 0, PolymorphicSerializer(Type::class))
                    1 -> elemType = decodeSerializableElement(descriptor, 1, PolymorphicSerializer(Type::class))
                    CompositeDecoder.DECODE_DONE -> break
                    else -> error("Unexpected index: $index")
                }
            }

            ArrayType(
                indexType = indexType ?: error("Missing indexType"),
                elemType = elemType ?: error("Missing elemType")
            )
        }
    }
}

// Configure the serialization module
val typeModule = SerializersModule {
    polymorphic(Type::class) {
        subclass(BoolType::class)
        subclass(IntType::class)
        subclass(StringType::class)
        subclass(ArrayType::class, ArrayTypeSerializer)
    }
}

val json = Json {
    serializersModule = typeModule
    classDiscriminator = "type"
}

// Usage example
fun main() {
    val bool: Type = BoolType
    val s1 = json.encodeToString(bool)
    println("Serialized: $s1")
    val d1 = json.decodeFromString<Type>(s1)
    println("Deserialized: $d1")

    val int: Type = IntType(42)
    val s2 = json.encodeToString(int)
    println("Serialized: $s2")
    val d2 = json.decodeFromString<Type>(s2)
    println("Deserialized: $d2")
    println((d2 as IntType).a)

    // Create a generic array type
    val intStringArray = ArrayType(
        indexType = IntType(1),
        elemType = StringType(2)
    )

    // Serialize using the wrapper approach
    val serialized = json.encodeToString(intStringArray)
    println("Serialized: $serialized")

    val deserialized = json.decodeFromString(serialized) as ArrayType<IntType, StringType>
    println("Deserialized: $deserialized")
    println(deserialized.indexType.a)


    val nestedArray = ArrayType(
        indexType = IntType(1),
        elemType = ArrayType(
            indexType = StringType(2),
            elemType = IntType(3)
        )
    )

    // Serialize using the wrapper approach
    val serialized2 = json.encodeToString(nestedArray)
    println("Serialized: $serialized2")

    val deserialized2 = json.decodeFromString(serialized2) as ArrayType<IntType, ArrayType<StringType, IntType>>
    println("Deserialized: $deserialized2")
    println(deserialized2.elemType.indexType.b)
}