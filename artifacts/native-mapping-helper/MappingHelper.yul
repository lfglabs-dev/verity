object "MappingHelper" {
 code {
  let result := mappingSlot(calldataload(0), calldataload(32))
  mstore(0, result)
  return(0, 32)
        function mappingSlot(baseSlot, key) -> slot {
            mstore(0, key)
            mstore(32, baseSlot)
            slot := keccak256(0, 64)
        }
 }
}
