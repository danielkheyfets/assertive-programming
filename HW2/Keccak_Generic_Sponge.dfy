/*
    // Daniel Kheyfets 20799333. Liel Keren 31574222
	Based on https://blog.adacore.com/avoiding-vulnerabilities-in-crypto-code-with-spark by Daniel King – Nov 04, 2022:
	this is a partial specification and re-implementation in Dafny of the SPARK/Ada Keccak generic sponge's Absorb procedure
	(https://github.com/damaki/libkeccak/blob/master/src/common/keccak-generic_sponge.adb).

	The goal here is to implement one method, Copy, and to verify correctness of another, Absorb (see TODO nodes below).
	Documentation of the proof obligations is expected here only for the Absorb method.
*/
const MAX := 0x7FFFFFFF // == (2^31)-1 == 2147483647
const State_Size_Bits := 500
const Block_Size_Bits := State_Size_Bits

const Naturals := set n: int | 0 <= n <= MAX
const Positives := set x: int | x in Naturals && 0 < x
const Rate_Bytes_Numbers := set m: int | m in Positives && m < (State_Size_Bits + 7) / 8
const Byte_Absorption_Numbers := set n: int | 0 <= n < (State_Size_Bits + 7) / 8
const Bit_Absorption_Numbers := set n: int | n in Naturals && 0 <= n < State_Size_Bits

newtype byte = x: int | -128 <= x < 128

// no need to implement the following method
// (in our context of verifying the absence of errors such as overflow in the generic implementation of "Absorb")
method XOR_bits_into_state(a: array<int>, data: seq<byte>, bit_len: nat)
	requires |data| <= a.Length && bit_len <= State_Size_Bits && (bit_len + 7) / 8 <= |data|
	modifies a
{}

// no need to implement the following method
// (in our context of verifying the absence of errors such as overflow in the generic implementation of "Absorb")
method Permute(state: array<int>)
	modifies state
	ensures multiset(state[..]) == multiset(old(state[..]))
{}

// TODO: implement this method; no need to document proof obligations
method Copy<T>(source: seq<T>, destination: array<T>, start: nat, end: nat)
	requires start < end <= destination.Length && |source| == end - start
	modifies destination
	ensures destination[..] == old(destination[..start]) + source + old(destination[end..])
{
  destination[start] := source[0];
  assert destination[..] == old(destination[..start]) + source[0.. 1] + old(destination[start + 1..]);

  var i := start + 1;
  while( i < end)
    invariant 0 <= i <= end
    invariant end - i <= |source|
    invariant destination[..] == old(destination[..start]) + source[0.. i-start] + old(destination[i..])
  {
    destination[i] := source[i- start];
    i := i +1;
  }
  assert destination[..] == old(destination[..start]) + source + old(destination[end..]);
}

predicate Precondition(state: array<int>, block: array<byte>, bits_absorbed: nat, rate: int, data: array<byte>, bit_length: nat) {
	0 < State_Size_Bits && rate <= block.Length <= |Byte_Absorption_Numbers| == state.Length &&
	bits_absorbed < State_Size_Bits && rate in Rate_Bytes_Numbers &&
	bit_length <= MAX - 7 && (bit_length + 7) / 8 <= data.Length &&
	bits_absorbed % 8 == 0 && bits_absorbed < rate * 8
}

predicate Postcondition1_No_Overflow(bits_absorbed: nat, offset: nat, remaining_bits: nat, remaining_bytes: nat, initial_data_len: nat, initial_bit_rate: int) {
	bits_absorbed in Bit_Absorption_Numbers && offset in Naturals && remaining_bits in Naturals && remaining_bytes in Naturals && initial_data_len in Naturals &&
	initial_bit_rate in Positives
}

predicate Postcondition2(bits_absorbed: nat, bit_length: nat, rate: int) {
	bits_absorbed % 8 == bit_length % 8 && bits_absorbed < rate * 8
}

// TODO: verify correctness of this method, documenting all proof obligations as we've learned;
// don't forget to remove the "{:verify false}" annotation (or turn it into "{:verify true}")
method {:verify true}  Absorb(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat)
		returns (bits_absorbed: nat, offset: nat, remaining_bits: nat, remaining_bytes: nat, initial_data_len: nat, initial_bit_rate: int)
	requires Precondition(state, block, bits_absorbed0, rate, data, bit_length)
	modifies state, block
	ensures Postcondition1_No_Overflow(bits_absorbed, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate)
	ensures Postcondition2(bits_absorbed, bit_length, rate)
{
  assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  bits_absorbed := bits_absorbed0;
  offset := 0;
  remaining_bits := bit_length;
  remaining_bytes := (bit_length + 7) / 8;
  initial_data_len := remaining_bytes;
  initial_bit_rate := rate * 8;

  assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  assert bits_absorbed == bits_absorbed0;
  assert offset == 0;
  assert remaining_bits == bit_length;
  assert remaining_bytes == (bit_length + 7) / 8;
  assert initial_data_len == remaining_bytes;
  assert initial_bit_rate == rate * 8;

  if initial_data_len > 0 {

    assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
    assert bits_absorbed == bits_absorbed0;
    assert offset == 0;
    assert remaining_bits == bit_length;
    assert remaining_bytes == (bit_length + 7) / 8;
    assert initial_data_len == remaining_bytes;
    assert initial_bit_rate == rate * 8;
    assert initial_data_len  > 0;

    var free_bytes_in_block: nat, free_bits_in_block: nat, block_offset: nat;
    // Calculate how many bits are free in the 'in' queue.
    free_bits_in_block := initial_bit_rate - bits_absorbed;
    free_bytes_in_block := free_bits_in_block / 8;

    assert free_bits_in_block == initial_bit_rate - bits_absorbed;
    assert free_bytes_in_block == free_bits_in_block / 8;
    assert free_bits_in_block < State_Size_Bits;
    assert free_bits_in_block % 8 == 0;
    assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
    assert bits_absorbed == bits_absorbed0;
    assert offset == 0;
    assert remaining_bits == bit_length;
    assert remaining_bytes == (bit_length + 7) / 8;
    assert initial_data_len == remaining_bytes;
    assert initial_bit_rate == rate * 8;
    assert initial_data_len  > 0;

    if bit_length < free_bits_in_block
    {
      assert bit_length < free_bits_in_block;
      assert free_bits_in_block == initial_bit_rate - bits_absorbed;
      assert free_bytes_in_block == free_bits_in_block / 8;
      assert free_bits_in_block < State_Size_Bits;
      assert free_bits_in_block % 8 == 0;
      assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
      assert bits_absorbed == bits_absorbed0;
      assert offset == 0;
      assert remaining_bits == bit_length;
      assert remaining_bytes == (bit_length + 7) / 8;
      assert initial_data_len == remaining_bytes;
      assert initial_bit_rate == rate * 8;
      assert initial_data_len  > 0;

      L_copy_precondition_2(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate,free_bits_in_block, free_bytes_in_block, bits_absorbed);
      assert bits_absorbed / 8 < bits_absorbed / 8 + remaining_bytes <= block.Length && |data[..initial_data_len]| == bits_absorbed / 8 + remaining_bytes - bits_absorbed / 8;
      block_offset := bits_absorbed / 8;
      assert block_offset < block_offset + remaining_bytes <= block.Length && |data[..initial_data_len]| == block_offset + remaining_bytes - block_offset;
      Copy(data[..initial_data_len], block, block_offset, block_offset + remaining_bytes);

      assert free_bits_in_block < State_Size_Bits;
      assert free_bits_in_block % 8 == 0;
      assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
      assert bits_absorbed == bits_absorbed0;
      assert offset == 0;
      assert remaining_bits == bit_length;
      assert remaining_bytes == (bit_length + 7) / 8;
      assert initial_data_len == remaining_bytes;
      assert initial_bit_rate == rate * 8;
      assert initial_data_len  > 0;
      assert bit_length < free_bits_in_block ;
      assert block_offset == bits_absorbed / 8;


      assert free_bits_in_block % 8 == 0;
      assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
      assert bits_absorbed == bits_absorbed0;
      assert offset == 0;
      assert remaining_bits == bit_length;
      assert remaining_bytes == (bit_length + 7) / 8;
      assert initial_data_len == remaining_bytes;
      assert initial_bit_rate == rate * 8;
      assert initial_data_len  > 0;
      assert bit_length < free_bits_in_block ;
      assert block_offset == bits_absorbed / 8;
      assert block_offset < block_offset + remaining_bytes <= block.Length && |data[..initial_data_len]| == block_offset + remaining_bytes - block_offset;
      assert bit_length < free_bits_in_block;
      assert free_bits_in_block == initial_bit_rate - bits_absorbed;
      assert free_bytes_in_block == free_bits_in_block / 8;
      //==>
      L_10(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate, bits_absorbed,block_offset,free_bits_in_block,free_bytes_in_block);
      L_11(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate, bits_absorbed,block_offset,free_bits_in_block,free_bytes_in_block);
      //==>
      assert Postcondition1_No_Overflow(bits_absorbed + bit_length, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate);
      assert Postcondition2(bits_absorbed + bit_length, bit_length, rate);
      bits_absorbed := bits_absorbed + bit_length;
      assert Postcondition1_No_Overflow(bits_absorbed, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate);
      assert Postcondition2(bits_absorbed, bit_length, rate);
    }
    else {
      assert free_bits_in_block < State_Size_Bits;
      assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
      assert initial_bit_rate == rate * 8;
      assert initial_data_len  >= 0;
      assert free_bits_in_block > 0;
      assert bits_absorbed < State_Size_Bits;
      assert free_bits_in_block % 8 == 0;
      assert bits_absorbed == bits_absorbed0;
      assert offset == 0;
      assert remaining_bits == bit_length;
      assert remaining_bytes == (bit_length + 7) / 8;
      assert initial_data_len == remaining_bytes;
      assert initial_bit_rate == rate * 8;
      assert initial_data_len  > 0;
      assert bit_length >= free_bits_in_block;
      assert free_bits_in_block == initial_bit_rate - bits_absorbed;
      assert free_bytes_in_block == free_bits_in_block / 8;
      assert initial_data_len  >= 0;
      // Append the first data to any leftovers to get a complete block.
      if free_bits_in_block > 0
      {
        assert free_bits_in_block < State_Size_Bits;
        assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
        assert initial_bit_rate == rate * 8;
        assert initial_data_len  >= 0;
        assert free_bits_in_block > 0;
        assert bits_absorbed < State_Size_Bits;
        assert free_bits_in_block % 8 == 0;
        assert bits_absorbed == bits_absorbed0;
        assert offset == 0;
        assert remaining_bits == bit_length;
        assert remaining_bytes == (bit_length + 7) / 8;
        assert initial_data_len == remaining_bytes;
        assert initial_bit_rate == rate * 8;
        assert initial_data_len  > 0;
        assert bit_length >= free_bits_in_block;
        assert free_bits_in_block == initial_bit_rate - bits_absorbed;
        assert free_bytes_in_block == free_bits_in_block / 8;

        copy_precondition_3(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate, bits_absorbed,free_bits_in_block,free_bytes_in_block);

        assert bits_absorbed / 8 < bits_absorbed / 8 + free_bytes_in_block <= block.Length && |data[..free_bytes_in_block]| == bits_absorbed / 8 + free_bytes_in_block - bits_absorbed / 8;
        block_offset := bits_absorbed / 8;
        assert block_offset < block_offset + free_bytes_in_block <= block.Length && |data[..free_bytes_in_block]| == block_offset + free_bytes_in_block - block_offset;
        Copy(data[..free_bytes_in_block], block, block_offset, block_offset + free_bytes_in_block);

        assert free_bits_in_block < State_Size_Bits;
        assert free_bits_in_block % 8 == 0;
        assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
        assert bits_absorbed == bits_absorbed0;
        assert offset == 0;
        assert bit_length >= free_bits_in_block;

        assert remaining_bits == bit_length;
        assert remaining_bytes == (bit_length + 7) / 8;
        assert initial_data_len == remaining_bytes;
        assert initial_bit_rate == rate * 8;
        assert initial_data_len  >= 0;
        assert free_bits_in_block > 0;
        assert bits_absorbed < State_Size_Bits;
        assert free_bytes_in_block == free_bits_in_block / 8;
        assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);


        L_2(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate, bits_absorbed,block_offset,free_bits_in_block,free_bytes_in_block);

        assert offset + free_bytes_in_block +  remaining_bytes - free_bytes_in_block == initial_data_len;
        assert  remaining_bytes - free_bytes_in_block == ( remaining_bits - free_bits_in_block + 7) / 8;
        assert initial_bit_rate < State_Size_Bits;
        assert  remaining_bytes - free_bytes_in_block - rate <= data.Length;
        assert initial_data_len < bit_length;
        assert initial_bit_rate == rate * 8;
        assert rate > 0;
        assert data.Length >= offset + free_bytes_in_block + remaining_bytes - free_bytes_in_block;
        assert 	initial_bit_rate == rate * 8;
        assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);


        offset := offset + free_bytes_in_block;
        remaining_bytes := remaining_bytes - free_bytes_in_block;
        remaining_bits := remaining_bits - free_bits_in_block;
        assert offset + remaining_bytes == initial_data_len;
        assert remaining_bytes == (remaining_bits + 7) / 8;
        assert initial_bit_rate < State_Size_Bits;
        assert remaining_bytes - rate <= data.Length;
        assert initial_data_len < bit_length;
        assert initial_bit_rate == rate * 8;
        assert rate > 0;
        assert data.Length >= offset + remaining_bytes;
        assert 	initial_bit_rate == rate * 8;
        assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);

      }

      assert offset + remaining_bytes == initial_data_len;
      assert remaining_bytes == (remaining_bits + 7) / 8;
      assert initial_bit_rate < State_Size_Bits;
      assert remaining_bytes - rate <= data.Length;
      assert initial_data_len < bit_length;
      assert initial_bit_rate == rate * 8;
      assert rate > 0;
      assert data.Length >= offset + remaining_bytes;
      assert 	initial_bit_rate == rate * 8;
      assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
      L_XOR_bits_into_state_1(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate, bits_absorbed,block_offset,free_bits_in_block,free_bytes_in_block);

      assert |block[..rate]| <= state.Length && initial_bit_rate <= State_Size_Bits && (initial_bit_rate + 7) / 8 <= |block[..rate]|;
      XOR_bits_into_state(state, block[..rate], initial_bit_rate);
      Permute(state);

      assert offset + remaining_bytes == initial_data_len;
      assert remaining_bytes == (remaining_bits + 7) / 8;
      assert initial_bit_rate < State_Size_Bits;
      assert remaining_bytes - rate <= data.Length;
      assert initial_data_len < bit_length;
      assert initial_bit_rate == rate * 8;
      assert rate > 0;
      assert data.Length >= offset + remaining_bytes;
      assert 	initial_bit_rate == rate * 8;
      L_while_precondition(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate);
      assert offset + remaining_bytes == initial_data_len;
      assert remaining_bytes <= data.Length;
      assert remaining_bytes == (remaining_bits + 7) / 8;
      assert (bit_length % 8) == (remaining_bits % 8);
      while remaining_bits >= initial_bit_rate
        invariant offset + remaining_bytes == initial_data_len
        invariant remaining_bytes <= data.Length
        invariant remaining_bytes == (remaining_bits + 7) / 8
        invariant (bit_length % 8) == (remaining_bits % 8)
        decreases remaining_bytes
        decreases remaining_bits

      {
        assert offset + remaining_bytes == initial_data_len;
        assert remaining_bytes == (remaining_bits + 7) / 8;
        assert initial_bit_rate < State_Size_Bits;
        assert remaining_bytes - rate <= data.Length;
        assert initial_data_len < bit_length;
        assert initial_bit_rate == rate * 8;
        assert rate > 0;
        assert offset + remaining_bytes == initial_data_len;
        assert remaining_bytes <= data.Length;
        assert remaining_bytes == (remaining_bits + 7) / 8;
        assert (bit_length % 8) == (remaining_bits % 8);

        L_1(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate);

        assert offset + rate + remaining_bytes - rate == initial_data_len;
        assert remaining_bytes - rate <= data.Length;
        assert remaining_bytes - rate == (remaining_bits - initial_bit_rate + 7) / 8;
        assert (bit_length % 8) == (remaining_bits % 8);
        assert offset + rate < bit_length;
        assert initial_data_len < bit_length;
        assert initial_bit_rate == rate * 8;
        assert rate > 0;
        assert |data[offset..offset + rate]| == rate;

        L_XOR_bits_into_state_2(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate);

        assert |data[offset..offset + rate]| <= state.Length && initial_bit_rate <= State_Size_Bits && (initial_bit_rate + 7) / 8 <= |data[offset..offset + rate]|;
        XOR_bits_into_state(state, data[offset..offset + rate], initial_bit_rate);

        assert offset + rate + remaining_bytes - rate == initial_data_len;
        assert remaining_bytes - rate <= data.Length;
        assert remaining_bytes - rate == (remaining_bits - initial_bit_rate + 7) / 8;
        assert (bit_length % 8) == (remaining_bits % 8);
        assert offset + rate < bit_length;
        assert initial_data_len < bit_length;
        assert initial_bit_rate == rate * 8;
        assert rate > 0;
        offset := offset + rate;
        remaining_bytes := remaining_bytes - rate;
        remaining_bits := remaining_bits - initial_bit_rate;
        assert offset + remaining_bytes == initial_data_len;
        assert remaining_bytes <= data.Length;
        assert remaining_bytes == (remaining_bits + 7) / 8;
        assert (bit_length % 8) == (remaining_bits % 8);
        assert offset < bit_length;
        assert initial_data_len < bit_length;
        assert initial_bit_rate == rate * 8;
        assert rate > 0;

      }
      assert offset + remaining_bytes == initial_data_len;
      assert remaining_bytes <= data.Length;
      assert remaining_bytes == (remaining_bits + 7) / 8;
      assert (bit_length % 8) == (remaining_bits % 8);
      assert offset < bit_length;
      assert initial_data_len < bit_length;
      assert initial_bit_rate == rate * 8;
      assert rate > 0;
      assert  remaining_bits < initial_bit_rate;
      assert initial_bit_rate < State_Size_Bits;

      L_while_postcondition(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate);

      assert offset + remaining_bytes == initial_data_len;
      assert remaining_bytes <= data.Length;
      assert remaining_bytes == (remaining_bits + 7) / 8;
      assert (bit_length % 8) == (remaining_bits % 8);
      assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
      assert remaining_bits < State_Size_Bits;
      assert offset < bit_length;
      assert initial_data_len < bit_length;
      assert initial_bit_rate == rate * 8;
      assert remaining_bits < initial_bit_rate;
      assert rate > 0;
      assert data.Length >= offset + remaining_bytes;

      // No more complete blocks. Store the leftovers
      if remaining_bits > 0 {
        assert offset + remaining_bytes == initial_data_len;
        assert remaining_bytes <= data.Length;
        assert remaining_bytes == (remaining_bits + 7) / 8;
        assert (bit_length % 8) == (remaining_bits % 8);
        assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
        assert remaining_bits < State_Size_Bits;
        assert offset < bit_length;
        assert initial_data_len < bit_length;
        assert initial_bit_rate == rate * 8;
        assert remaining_bits < initial_bit_rate;
        assert rate > 0;
        assert remaining_bits > 0;
        assert data.Length >= offset + remaining_bytes;

        copy_precondition_1(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate);

        assert 0 < remaining_bytes <= block.Length && |data[offset..offset + remaining_bytes]| == remaining_bytes - 0;
        Copy(data[offset..offset + remaining_bytes], block, 0, remaining_bytes);
        assert offset + remaining_bytes == initial_data_len;
        assert remaining_bytes <= data.Length;
        assert remaining_bytes == (remaining_bits + 7) / 8;
        assert (bit_length % 8) == (remaining_bits % 8);
        assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
        assert remaining_bits < State_Size_Bits;
        assert offset < bit_length;
        assert initial_data_len < bit_length;
        assert initial_bit_rate == rate * 8;
        assert remaining_bits < initial_bit_rate;
        assert rate > 0;
      }
      assert offset + remaining_bytes == initial_data_len;
      assert remaining_bytes <= data.Length;
      assert remaining_bytes == (remaining_bits + 7) / 8;
      assert (bit_length % 8) == (remaining_bits % 8);
      assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
      assert remaining_bits < State_Size_Bits;
      assert offset < bit_length;
      assert initial_data_len < bit_length;
      assert initial_bit_rate == rate * 8;
      assert remaining_bits < initial_bit_rate;
      assert rate > 0;
      L_postcondition_1(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate);
      L_postcondition_2(state, block, bits_absorbed0, rate, data, bit_length, remaining_bytes, remaining_bits,offset,initial_data_len,initial_bit_rate);
      assert Postcondition1_No_Overflow(remaining_bits, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate);
      assert Postcondition2(remaining_bits, bit_length, rate);
      bits_absorbed := remaining_bits;
      assert Postcondition1_No_Overflow(bits_absorbed, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate);
      assert Postcondition2(bits_absorbed, bit_length, rate);


    }
  }
}


lemma L_2(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int, bits_absorbed: nat,block_offset:nat,free_bits_in_block:int,free_bytes_in_block:int)
  requires free_bits_in_block % 8 == 0;
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires offset == 0;
  requires remaining_bits == bit_length;
  requires remaining_bytes == (bit_length + 7) / 8;
  requires initial_data_len == remaining_bytes;
  requires initial_bit_rate == rate * 8;
  requires free_bits_in_block > 0;
  requires bit_length >= free_bits_in_block;
  requires free_bytes_in_block == free_bits_in_block / 8;

  //
  ensures offset + free_bytes_in_block +  remaining_bytes - free_bytes_in_block == initial_data_len;
  ensures  remaining_bytes - free_bytes_in_block == ( remaining_bits - free_bits_in_block + 7) / 8;
  ensures initial_bit_rate < State_Size_Bits;
  ensures  remaining_bytes - free_bytes_in_block - rate <= data.Length;
  ensures initial_data_len < bit_length;
  ensures initial_bit_rate == rate * 8;
  ensures rate > 0;
  ensures data.Length >= offset + free_bytes_in_block + remaining_bytes - free_bytes_in_block;
  ensures initial_bit_rate == rate * 8;
{
  assert  initial_bit_rate == rate * 8 by {
    assert initial_bit_rate == rate * 8;
  }

  assert  data.Length >= offset + free_bytes_in_block + remaining_bytes - free_bytes_in_block by {
    assert  data.Length >= offset + remaining_bytes;
    assert (bit_length + 7) / 8 <= data.Length;
    assert remaining_bytes == (bit_length + 7) / 8;
    assert remaining_bytes <= data.Length;
    assert remaining_bytes <= data.Length+offset ;

    assert  data.Length >= offset + free_bytes_in_block + remaining_bytes - free_bytes_in_block;

  }

  assert  rate > 0 by {
    assert rate in Rate_Bytes_Numbers;
    assert  rate > 0;
  }

  assert  initial_bit_rate == rate * 8 by {
    assert  initial_bit_rate == rate * 8;
  }
  assert  initial_data_len < bit_length by {
    assert remaining_bytes == (bit_length + 7) / 8;
    assert initial_data_len == remaining_bytes;
    assert initial_data_len == (bit_length + 7) / 8;

    assert initial_data_len < bit_length;


    assert  initial_data_len < bit_length;

  }

  assert  remaining_bytes - free_bytes_in_block - rate <= data.Length by {

    assert initial_data_len < bit_length;
    assert initial_data_len == remaining_bytes;
    assert remaining_bytes  < bit_length;
    assert (bit_length + 7) / 8 <= data.Length; //pre

    assert  remaining_bytes - free_bytes_in_block - rate <= data.Length;

  }

  assert offset + free_bytes_in_block +  remaining_bytes - free_bytes_in_block == initial_data_len by {
    assert offset == 0;
    assert initial_data_len == remaining_bytes;
    //         =>
    assert offset + free_bytes_in_block +  remaining_bytes - free_bytes_in_block == initial_data_len;

  }
  assert remaining_bytes - free_bytes_in_block == ( remaining_bits - free_bits_in_block + 7) / 8 by {
    assert remaining_bytes == (bit_length + 7) / 8;
    assert remaining_bits == bit_length;
    assert (bit_length + 7) / 8 - free_bytes_in_block == ( remaining_bits - free_bits_in_block + 7) / 8;
    assert (remaining_bits + 7) / 8 - free_bytes_in_block == ( remaining_bits - free_bits_in_block + 7) / 8;

    assert free_bytes_in_block == free_bits_in_block / 8;
    //         =>
    assert remaining_bytes - free_bytes_in_block == ( remaining_bits - free_bits_in_block + 7) / 8;

  }

}



lemma  L_XOR_bits_into_state_1(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int, bits_absorbed: nat,block_offset:nat,free_bits_in_block:int,free_bytes_in_block:int)
  requires offset + remaining_bytes == initial_data_len;
  requires remaining_bytes == (remaining_bits + 7) / 8;
  requires initial_bit_rate < State_Size_Bits;
  requires remaining_bytes - rate <= data.Length;
  requires initial_data_len < bit_length;
  requires initial_bit_rate == rate * 8;
  requires rate > 0;
  requires data.Length >= offset + remaining_bytes;
  requires 	initial_bit_rate == rate * 8;
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);


  ensures |block[..rate]| <= state.Length && initial_bit_rate <= State_Size_Bits && (initial_bit_rate + 7) / 8 <= |block[..rate]|;
{
  assert |block[..rate]| <= state.Length by {
    assert |Byte_Absorption_Numbers| == state.Length; //pre
    assert  rate <= block.Length;//pre;
    assert block.Length <= state.Length;

    assert |block[..rate]| <= state.Length;

  }
  assert initial_bit_rate <= State_Size_Bits by {
    //         =>
    assert initial_bit_rate < State_Size_Bits;

  }
  assert  (initial_bit_rate + 7) / 8 <= |block[..rate]| by {
    assert initial_bit_rate == rate * 8;
    assert  (initial_bit_rate + 7) / 8 <= rate;
    //         =>
    assert  (initial_bit_rate + 7) / 8 <= |block[..rate]|;

  }
}
lemma L_11(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int, bits_absorbed: nat,block_offset:nat,free_bits_in_block:int,free_bytes_in_block:int)


  requires free_bits_in_block % 8 == 0;
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires bits_absorbed == bits_absorbed0;
  requires offset == 0;
  requires remaining_bits == bit_length;
  requires remaining_bytes == (bit_length + 7) / 8;
  requires initial_data_len == remaining_bytes;
  requires initial_bit_rate == rate * 8;
  requires initial_data_len  > 0;
  requires bit_length < free_bits_in_block ;
  requires block_offset == bits_absorbed / 8;
  requires block_offset < block_offset + remaining_bytes <= block.Length && |data[..initial_data_len]| == block_offset + remaining_bytes - block_offset;
  requires bit_length < free_bits_in_block;
  requires free_bits_in_block == initial_bit_rate - bits_absorbed;
  requires free_bytes_in_block == free_bits_in_block / 8;


  ensures Postcondition1_No_Overflow(bits_absorbed + bit_length, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate);
{

}


lemma L_10(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int, bits_absorbed: nat,block_offset:nat,free_bits_in_block:int,free_bytes_in_block:int)

  requires free_bits_in_block % 8 == 0;
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires bits_absorbed == bits_absorbed0;
  requires offset == 0;
  requires remaining_bits == bit_length;
  requires remaining_bytes == (bit_length + 7) / 8;
  requires initial_data_len == remaining_bytes;
  requires initial_bit_rate == rate * 8;
  requires bit_length < free_bits_in_block ;
  requires free_bits_in_block == initial_bit_rate - bits_absorbed;
  requires free_bytes_in_block == free_bits_in_block / 8;
  ensures remaining_bits % 8 == bit_length % 8
  ensures remaining_bits < rate * 8;
  ensures Postcondition2(bits_absorbed + bit_length, bit_length, rate);
{
  assert remaining_bits % 8 == bit_length % 8 by {
    assert remaining_bits == bit_length;
    //         =>
    assert  remaining_bits % 8 == bit_length % 8;

  }
  assert remaining_bits < rate * 8 by {
    assert remaining_bits == bit_length;//assert bit_length < rate * 8
    assert bit_length < free_bits_in_block ;//==initial_bit_rate - bits_absorbed;  //assert bit_length < rate * 8
    assert free_bits_in_block == initial_bit_rate - bits_absorbed;
    assert initial_bit_rate == rate * 8;
    //         =>
    assert free_bits_in_block == rate * 8 - bits_absorbed;
    assert bit_length < rate * 8 - bits_absorbed;
    assert remaining_bits < rate * 8 - bits_absorbed;
    //         =>
    assert  remaining_bits < rate * 8;

  }
}





lemma L_while_precondition(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int)

  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires remaining_bytes == (remaining_bits + 7) / 8;
  requires initial_bit_rate < State_Size_Bits;
  requires remaining_bytes - rate <= data.Length;
  requires initial_data_len < bit_length;//need to proof
  requires initial_bit_rate == rate * 8; ////need to proof
  requires rate > 0;
  requires data.Length >= offset + remaining_bytes;

  ensures remaining_bytes <= data.Length;
  ensures remaining_bytes <= data.Length;
{
  assert remaining_bytes <= data.Length by {
    assert offset>=0;
    assert  data.Length >= offset + remaining_bytes;  //remaining_bytes<=data.Length - offset
    //         =>
    assert  remaining_bytes <= data.Length;

  }

}

lemma L_XOR_bits_into_state_2(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int)
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires remaining_bytes - rate == (remaining_bits - initial_bit_rate + 7) / 8;
  requires initial_data_len < bit_length;//need to proof
  requires initial_bit_rate == rate * 8; ////need to proof
  requires data.Length >= offset + remaining_bytes;
  requires remaining_bits >= initial_bit_rate;


  ensures  |data[offset..offset + rate]| <= state.Length && initial_bit_rate <= State_Size_Bits && (initial_bit_rate + 7) / 8 <= |data[offset..offset + rate]|

{

  assert |data[offset..offset + rate]| <= state.Length by {
    assert rate<=  state.Length ;
    assert |data[offset..offset + rate]| == rate;
    //         =>
    assert  |data[offset..offset + rate]| <= state.Length;

  }

  //
  assert (initial_bit_rate + 7) / 8 <= |data[offset..offset + rate]| by {
    assert |data[offset..offset + rate]| == rate;
    assert initial_bit_rate == rate * 8;
    //         =>
    assert  (initial_bit_rate + 7) / 8 <= |data[offset..offset + rate]|;

  }


}

// const Naturals := set n: int | 0 <= n <= MAX
// const Positives := set x: int | x in Naturals && 0 < x
// const Rate_Bytes_Numbers := set m: int | m in Positives && m < (State_Size_Bits + 7) / 8
// const Byte_Absorption_Numbers := set n: int | 0 <= n < (State_Size_Bits + 7) / 8
// const Bit_Absorption_Numbers := set n: int | n in Naturals && 0 <= n < State_Size_Bits
lemma L_postcondition_1(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int)
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires remaining_bytes == (remaining_bits + 7) / 8;
  requires remaining_bits < State_Size_Bits;
  requires initial_data_len < bit_length;
  requires initial_bit_rate == rate * 8;
  requires offset < bit_length
  ensures remaining_bits in Bit_Absorption_Numbers
  ensures offset in Naturals
  ensures remaining_bits in Naturals
  ensures remaining_bytes in Naturals
  ensures initial_data_len in Naturals
  ensures initial_bit_rate in Positives
  ensures Postcondition1_No_Overflow(remaining_bits, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate);
{
  assert remaining_bits in Bit_Absorption_Numbers by {
    assert remaining_bits is nat;
    assert remaining_bits < State_Size_Bits;
    assert remaining_bits <= MAX; {assert remaining_bits < State_Size_Bits == 500;}
    assert 0<= remaining_bits;
  }

  assert offset in Naturals by{
    assert offset is nat;
    assert 0<= offset <bit_length<= MAX - 7;
  }

  assert remaining_bits in Naturals by{
    assert remaining_bits is nat;
    assert 0 <= remaining_bits;
    assert remaining_bits < State_Size_Bits < MAX;
  }

  assert initial_data_len in Naturals by {
    assert initial_data_len is nat;
    assert 0 <= initial_data_len;
    assert initial_data_len < bit_length <= MAX - 7;
  }

  assert initial_bit_rate in Positives by{
    assert initial_bit_rate is int;
    //=>
    assert 0 <= initial_bit_rate;
    assert initial_bit_rate == rate * 8 < MAX;
    //=>
    assert initial_bit_rate in Naturals;
  }

  assert Postcondition1_No_Overflow(remaining_bits, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate);
}

lemma copy_precondition_3(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int, bits_absorbed: int,free_bits_in_block:int,free_bytes_in_block:int)
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires free_bits_in_block > 0;
  requires bits_absorbed < State_Size_Bits;
  requires free_bits_in_block % 8 == 0;
  requires bits_absorbed == bits_absorbed0;
  requires offset == 0;
  requires remaining_bytes == (bit_length + 7) / 8;
  requires initial_data_len == remaining_bytes;
  requires initial_bit_rate == rate * 8;
  requires bit_length >= free_bits_in_block
  requires free_bits_in_block == initial_bit_rate - bits_absorbed;
  requires free_bytes_in_block == free_bits_in_block / 8;
  ensures bits_absorbed / 8 < bits_absorbed / 8 + free_bytes_in_block <= block.Length && |data[..free_bytes_in_block]| == bits_absorbed / 8 + free_bytes_in_block - bits_absorbed / 8
{
  assert |data[..free_bytes_in_block]| == bits_absorbed / 8 + free_bytes_in_block - bits_absorbed / 8  by {
    assert  bits_absorbed / 8 + free_bytes_in_block - bits_absorbed / 8 == free_bytes_in_block;
    //         =>
    assert  |data[..free_bytes_in_block]| == bits_absorbed / 8 + free_bytes_in_block - bits_absorbed / 8 ;

  }

  assert  bits_absorbed / 8 < bits_absorbed / 8 + free_bytes_in_block <= block.Length by {
    assert free_bytes_in_block == free_bits_in_block / 8; // free_bits_in_block =free_bytes_in_block*8
    assert free_bits_in_block > 0;
    //         =>
    assert  bits_absorbed / 8 < bits_absorbed / 8 + free_bytes_in_block;


    assert rate <= block.Length; //from the Precondition
    assert bits_absorbed < rate * 8;//bits_absorbed/8 <  rate  from the Precondition
    assert initial_bit_rate == rate * 8;
    assert bit_length >= free_bits_in_block;
    assert free_bits_in_block == initial_bit_rate - bits_absorbed;
    assert free_bytes_in_block == free_bits_in_block / 8;
    //         =>
    assert  bits_absorbed / 8 + free_bytes_in_block <= block.Length;


    assert  bits_absorbed / 8 < bits_absorbed / 8 + free_bytes_in_block;
    assert  bits_absorbed / 8 + free_bytes_in_block <= block.Length;
    //         =>
    assert  bits_absorbed / 8 < bits_absorbed / 8 + free_bytes_in_block <= block.Length;
  }



}


lemma copy_precondition_1(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int)
  requires remaining_bytes == (remaining_bits + 7) / 8; // **
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires initial_bit_rate == rate * 8;
  requires remaining_bits < initial_bit_rate;
  requires remaining_bits > 0; // *
  requires data.Length >= offset + remaining_bytes;
  ensures 0 < remaining_bytes <= block.Length
  ensures |data[offset..offset + remaining_bytes]| == remaining_bytes - 0;
{
  assert 0 < remaining_bytes <= block.Length by {
    assert Precondition(state, block, bits_absorbed0, rate, data, bit_length);
    assert  rate <= block.Length ;
    assert remaining_bits < initial_bit_rate;
    assert initial_bit_rate == rate * 8;
    assert remaining_bytes == (remaining_bits + 7) / 8; // **
    assert remaining_bits < rate * 8 <= block.Length * 8;
    //==>
    assert 8 * remaining_bytes - 7  <= block.Length * 8;
    assert remaining_bytes - 7 <= block.Length;
    assert remaining_bytes - 7 <= block.Length;
    assert remaining_bytes  <= block.Length;


    assert remaining_bytes == (remaining_bits + 7) / 8; // **
    assert remaining_bits > 0; //by *
    //==>
    assert remaining_bytes > 0;

  }

  assert |data[offset..offset + remaining_bytes]| == remaining_bytes - 0 by {
    assert  0 < remaining_bytes;
    assert data.Length >= offset + remaining_bytes;
  }

}

lemma L_copy_precondition_2(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int, free_bits_in_block: int, free_bytes_in_block:int, bits_absorbed: nat)
  requires bit_length < free_bits_in_block;
  requires free_bits_in_block == initial_bit_rate - bits_absorbed;
  requires free_bytes_in_block == free_bits_in_block / 8;
  requires free_bits_in_block < State_Size_Bits;
  requires free_bits_in_block % 8 == 0;
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires bits_absorbed == bits_absorbed0;
  requires offset == 0;
  requires remaining_bits == bit_length;
  requires remaining_bytes == (bit_length + 7) / 8;
  requires initial_data_len == remaining_bytes;
  requires initial_bit_rate == rate * 8;
  requires initial_data_len  > 0;
  ensures bits_absorbed / 8 < bits_absorbed / 8 + remaining_bytes <= block.Length && |data[..initial_data_len]| == bits_absorbed / 8 + remaining_bytes - bits_absorbed / 8
{
  assert bits_absorbed / 8 < bits_absorbed / 8 + remaining_bytes <= block.Length && |data[..initial_data_len]| == bits_absorbed / 8 + remaining_bytes - bits_absorbed / 8 by {

    assert initial_data_len == remaining_bytes;
    //         =>
    assert  |data[..initial_data_len]| == bits_absorbed / 8 + remaining_bytes - bits_absorbed / 8;



    assert initial_data_len == remaining_bytes;
    assert  initial_data_len  > 0;
    //         =>
    assert  bits_absorbed / 8 < bits_absorbed / 8 + remaining_bytes ;

    assert  Precondition(state, block, bits_absorbed0, rate, data, bit_length);
    assert rate <= block.Length; //from the Precondition
    assert free_bits_in_block == initial_bit_rate - bits_absorbed; //bits_absorbed = initial_bit_rate - free_bits_in_block
    assert initial_bit_rate == rate * 8;
    assert initial_data_len == remaining_bytes;
    //         =>
    assert  bits_absorbed / 8 + remaining_bytes <= block.Length;//rate //initial_bit_rate/8


    //         =>  => => => => =>
    assert  bits_absorbed / 8 < bits_absorbed / 8 + remaining_bytes <= block.Length && |data[..initial_data_len]| == bits_absorbed / 8 + remaining_bytes - bits_absorbed / 8;

  }
}
lemma L_postcondition_2(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: nat, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int)
  requires Precondition(state, block, bits_absorbed0, rate, data, bit_length);
  requires (bit_length % 8) == (remaining_bits % 8);
  requires remaining_bits < initial_bit_rate;
  requires initial_bit_rate == 8 * rate;
  ensures remaining_bits % 8 == bit_length % 8
  ensures remaining_bits < rate * 8;
  ensures Postcondition2(remaining_bits, bit_length, rate)
{
  assert (bit_length % 8) == (remaining_bits % 8);
  //=>
  assert remaining_bits % 8 == bit_length % 8 ;

  assert remaining_bits < initial_bit_rate;
  assert initial_bit_rate == 8 * rate;
  //=>
  assert remaining_bits < rate * 8;

  //=>
  assert Postcondition2(remaining_bits, bit_length, rate);
}


lemma L_while_postcondition(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: int, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int)
  requires offset + remaining_bytes == initial_data_len; // 1
  requires remaining_bytes <= data.Length; // 2
  requires remaining_bytes == (remaining_bits + 7) / 8;// 3
  requires (bit_length % 8) == (remaining_bits % 8);// 4
  requires offset < bit_length; // 5
  requires initial_data_len < bit_length;//6
  requires initial_bit_rate == rate * 8; //7
  requires rate > 0; // 8
  requires  remaining_bits < initial_bit_rate; //9
  requires initial_bit_rate < State_Size_Bits; //10

  ensures offset + remaining_bytes == initial_data_len;
  ensures remaining_bytes <= data.Length;
  ensures remaining_bytes == (remaining_bits + 7) / 8;
  ensures (bit_length % 8) == (remaining_bits % 8);
  ensures remaining_bits < State_Size_Bits;
  ensures offset < bit_length;
  ensures initial_data_len < bit_length;
  ensures initial_bit_rate == rate * 8;
  ensures remaining_bits < initial_bit_rate;
  ensures rate > 0;
{
  assert offset + remaining_bytes == initial_data_len; // by 1
  assert remaining_bytes <= data.Length; //by 2
  assert remaining_bytes == (remaining_bits + 7) / 8; //by 3
  assert (bit_length % 8) == (remaining_bits % 8); //by 4
  assert offset < bit_length; //by 5
  assert initial_data_len < bit_length; //by 6
  assert initial_bit_rate == rate * 8;// by 7
  assert remaining_bits < initial_bit_rate; //by 9
  assert rate > 0; // by 8
  assert remaining_bits < State_Size_Bits by {
    assert remaining_bits < initial_bit_rate;
    assert initial_bit_rate < State_Size_Bits;
    //==>
    assert remaining_bits < State_Size_Bits;
  }

}


lemma L_1(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat, remaining_bytes: int, remaining_bits:nat,offset:nat,initial_data_len:nat,initial_bit_rate:int)
  requires offset + remaining_bytes == initial_data_len;
  requires remaining_bytes <= data.Length;
  requires remaining_bytes == (remaining_bits + 7) / 8;
  requires (bit_length % 8) == (remaining_bits % 8);
  requires remaining_bits >= initial_bit_rate;
  requires offset + remaining_bytes == initial_data_len;
  requires remaining_bytes == (remaining_bits + 7) / 8;
  requires initial_bit_rate < State_Size_Bits;
  requires remaining_bytes - rate <= data.Length;
  requires initial_data_len < bit_length;
  requires initial_bit_rate == rate * 8;
  requires rate > 0;



  ensures offset + rate + remaining_bytes - rate == initial_data_len;
  ensures remaining_bytes - rate <= data.Length;
  ensures remaining_bytes - rate == (remaining_bits - initial_bit_rate + 7) / 8;
  ensures (bit_length % 8) == (remaining_bits % 8);
  ensures offset + rate < bit_length;
  ensures initial_data_len < bit_length;
  ensures initial_bit_rate == rate * 8;
  ensures rate > 0;
{

  assert (bit_length % 8) == (remaining_bits % 8 )by {
    //         =>

    assert (bit_length % 8) == (remaining_bits % 8);

  }
  assert remaining_bytes - rate == (remaining_bits - initial_bit_rate + 7) / 8 by {
    assert remaining_bytes == (remaining_bits + 7) / 8;
    assert  initial_bit_rate == rate * 8;
    //         =>
    assert  remaining_bytes - rate == (remaining_bits - initial_bit_rate + 7) / 8;

  }
  assert remaining_bytes - rate <= data.Length by {
    assert remaining_bytes <= data.Length;
    assert rate > 0;
    //         =>
    assert  remaining_bytes - rate <= data.Length;

  }

  assert offset + rate + remaining_bytes - rate == initial_data_len by {
    assert offset + remaining_bytes == initial_data_len;
    //         =>
    assert  offset + rate + remaining_bytes - rate == initial_data_len;
  }


  assert offset + rate < bit_length by {
    assert offset + remaining_bytes == initial_data_len;
    assert remaining_bytes - rate <= data.Length;
    assert initial_data_len < bit_length;
    assert rate > 0;
    //         =>
    assert offset + rate < bit_length ;

  }
  assert initial_bit_rate == rate * 8 by {
    //         =>
    assert initial_bit_rate == rate * 8;
  }

  assert initial_data_len < bit_length by {
    //         =>
    assert initial_data_len < bit_length;
  }
  assert rate > 0 by {
    //         =>
    assert rate > 0;
  }
}

