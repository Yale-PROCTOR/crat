#![feature(derive_clone_copy)]
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types, non_snake_case)]
pub type size_t = u64;
pub struct BlockEncoder {
    pub histogram_length_: size_t,
    pub num_block_types_: size_t,
    pub block_types_: *const u8,
    pub block_lengths_: *const u32,
    pub num_blocks_: size_t,
}
unsafe extern "C" fn BuildAndStoreBlockSplitCode(
    mut types: *const u8,
    mut lengths: *const u32,
    mut num_blocks: size_t,
) -> u32 {
    let mut i: size_t = 0;
    let mut acc: u32 = 0;
    while i < num_blocks {
        acc = acc.wrapping_add(*types.offset(i as isize) as u32).wrapping_add(*lengths.offset(i as isize));
        i = i.wrapping_add(1);
    }
    return acc;
}
unsafe extern "C" fn InitBlockEncoder(
    mut self_0: *mut BlockEncoder,
    mut histogram_length: size_t,
    mut num_block_types: size_t,
    mut block_types: *const u8,
    mut block_lengths: *const u32,
    num_blocks: size_t,
) {
    (*self_0).histogram_length_ = histogram_length;
    (*self_0).num_block_types_ = num_block_types;
    let ref mut fresh10 = (*self_0).block_types_;
    *fresh10 = block_types;
    let ref mut fresh11 = (*self_0).block_lengths_;
    *fresh11 = block_lengths;
    (*self_0).num_blocks_ = num_blocks;
}
unsafe extern "C" fn BuildAndStoreBlockSwitchEntropyCodes(mut self_0: *mut BlockEncoder) -> u32 {
    return BuildAndStoreBlockSplitCode((*self_0).block_types_, (*self_0).block_lengths_, (*self_0).num_blocks_);
}
unsafe extern "C" fn StoreSymbol(mut self_0: *mut BlockEncoder, mut block_ix: size_t) -> u8 {
    let mut block_type = *((*self_0).block_types_).offset(block_ix as isize);
    return block_type;
}
#[no_mangle]
pub unsafe extern "C" fn Drive(mut types: *const u8, mut lengths: *const u32, mut num_blocks: size_t) -> u32 {
    let mut encoder = BlockEncoder {
        histogram_length_: 0,
        num_block_types_: 0,
        block_types_: 0 as *const u8,
        block_lengths_: 0 as *const u32,
        num_blocks_: 0,
    };
    InitBlockEncoder(&mut encoder, 256 as size_t, 2 as size_t, types, lengths, num_blocks);
    let mut s = BuildAndStoreBlockSwitchEntropyCodes(&mut encoder) as u32;
    return s.wrapping_add(StoreSymbol(&mut encoder, 0 as size_t) as u32);
}
