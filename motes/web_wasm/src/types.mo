/// Opaque browser handles. A `Node` is a JS node id; a `RequestId` names an
/// in-flight two-phase fetch. Neither is ever constructed, matched or
/// compared; they only cross the extern boundary.

pub type Node { node }
pub type RequestId { request_id }
pub type ClipboardOp { clipboard_op }
