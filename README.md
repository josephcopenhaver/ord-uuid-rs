# ord-uuid-rs

Creates lexically sortable uuid values of size 16 bytes.

All functions of the OrdUuidGen type that return an OrdUuid will be naturally sortable based on creation time. All bits not related to ensuring uniqueness are shifted to the least significant bits.
